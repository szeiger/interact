package de.szeiger.interact

import fastparse._

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

object AST {
  sealed trait Statement
  case class Cons(name: String, args: Seq[String], operator: Boolean, ret: Option[String], der: Option[Deriving]) extends Statement {
    def show: String = {
      val a = if(args.isEmpty) "" else args.mkString("(", ", ", ")")
      val r = if(ret.isEmpty) "" else s" . ${ret.get}"
      val d = if(der.isEmpty) "" else s" deriving ${der.get.show}"
      s"$name$a$r$d"
    }
  }
  case class Deriving(constructors: Seq[String]) {
    def show = constructors.mkString(", ")
  }
  trait Expr {
    def show: String
    def allIdents: Iterator[Ident]
  }
  case class Ident(s: String) extends Expr {
    def show = s
    def allIdents: Iterator[Ident] = Iterator.single(this)
  }
  case object Wildcard extends Expr {
    def show = "_"
    def allIdents: Iterator[Ident] = Iterator.empty
  }
  case class Assignment(lhs: Expr, rhs: Expr) extends Expr {
    def show = s"${lhs.show} = ${rhs.show}"
    def allIdents = lhs.allIdents ++ rhs.allIdents
  }
  case class Tuple(exprs: Seq[Expr]) extends Expr {
    def show = exprs.map(_.show).mkString("(", ", ", ")")
    def allIdents: Iterator[Ident] = exprs.iterator.flatMap(_.allIdents)
  }
  case class Ap(target: Ident, args: Seq[Expr]) extends Expr {
    def show = args.iterator.map(_.show).mkString(s"${target.show}(", ", ", ")")
    def allIdents: Iterator[Ident] = Iterator.single(target) ++ args.iterator.flatMap(_.allIdents)
  }
  case class Data(defs: Seq[Expr]) extends Statement {
    def show = defs.map(_.show).mkString(", ")
    var free: Seq[String] = _
  }
  case class Def(name: String, args: Seq[String], operator: Boolean, ret: Seq[String], rules: Seq[DefRule]) extends Statement {
    def show: String = {
      val a = if(args.isEmpty) "" else args.map(s => if(s == null) "_" else s).mkString("(", ", ", ")")
      val r = if(ret.isEmpty) "" else if(ret.length == 1) ret.head else ret.mkString("(", ", ", ")")
      s"$name$a: $r"
    }
  }
  case class DefRule(on: Seq[Expr], reduced: Seq[Expr])
  case class Match(on: Expr, reduced: Seq[Expr]) extends Statement {
    def show = s"${on.show} => ${reduced.map(_.show).mkString(", ")}"
  }

  object IdentOrAp {
    def unapply(e: Expr): Option[(String, Seq[Expr])] = e match {
      case Ident(s) => Some((s, Nil))
      case Ap(Ident(s), a) => Some((s, a))
      case _ => None
    }
  }
  object SimpleExprSpec {
    def unapply(e: Expr): Option[(String, Seq[Expr])] = e match {
      case Ident(s) => Some((s, Nil))
      case Ap(Ident(s), a) => Some((s, a))
      case Wildcard => Some((null, Nil))
      case Tuple(args) => Some((null, args))
    }
  }
  object IdentOrTuple {
    def unapply(e: Expr): Option[Seq[Expr]] = e match {
      case i: Ident => Some(Seq(i))
      case Tuple(es) => Some(es)
      case _ => None
    }
  }
}

object Lexical {
  import NoWhitespace._

  val keywords = Set("cons", "let", "deriving", "def", "match", "_")
  private val operatorStart = IndexedSeq(Set('*', '/', '%'), Set('+', '-'), Set(':'), Set('<', '>'), Set('&'), Set('^'), Set('|'))
  private val operatorCont = operatorStart.iterator.flatten.toSet
  private val notAnOperator = Set(":", "=", "=>", "|")
  val MaxPrecedence = operatorStart.length-1

  def precedenceOf(s: String): Int =
    if(notAnOperator.contains(s) || !s.forall(operatorCont.contains)) -1
    else { val c = s.charAt(0); operatorStart.indexWhere(_.contains(c)) }
  def isRightAssoc(s: String): Boolean = s.endsWith(":")

  def ident[_: P]: P[String] =
     P(  (letter|"_") ~ (letter | digit | "_").rep  ).!.filter(!keywords.contains(_))
  def kw[_: P](s: String) = P(  s ~ !(letter | digit | "_")  )
  def letter[_: P] = P( CharIn("a-z") | CharIn("A-Z") )
  def digit[_: P] = P( CharIn("0-9") )
  def churchLit[_: P] = P(  digit.rep(1).! ~ "'c"  ).map(_.toInt)

  def operator[_: P](precedence: Int): P[String] =
    P(  CharPred(operatorStart(precedence).contains) ~ CharPred(operatorCont.contains).rep  ).!.filter(s => !notAnOperator.contains(s))

  def anyOperator[_: P]: P[String] =
    P(  CharPred(operatorCont.contains).rep(1)  ).!.filter(s => !notAnOperator.contains(s))
}

object Parser {
  import ScriptWhitespace._
  import Lexical._

  def identExpr[_: P]: P[AST.Ident] = ident.map(AST.Ident)

  def wildcard[_: P]: P[AST.Wildcard.type] = P("_").map(_ => AST.Wildcard)

  def church[_: P]: P[AST.Expr] = churchLit.map { i =>
    (1 to i).foldLeft(AST.Ident("Z"): AST.Expr) { case (z, _) => AST.Ap(AST.Ident("S"), z :: Nil) }
  }

  def app[_: P]: P[AST.Ap] =
    P(  identExpr ~ "(" ~ expr.rep(sep = ",") ~ ")"  ).map(AST.Ap.tupled)

  def tuple[_: P]: P[AST.Tuple] =
    P(  "(" ~ expr.rep(min = 0, sep = ",") ~ ")"  ).map(AST.Tuple)

  def simpleExpr[_: P]: P[AST.Expr] =
    P(  (app | identExpr | wildcard | church | tuple)  )

  def operatorEx[_: P](precedence: Int): P[AST.Expr] = {
    def next = if(precedence == 0) simpleExpr else operatorEx(precedence - 1)
    P(  next ~ (operator(precedence) ~ next).rep  ).map {
      case (e, Seq()) => e
      case (e, ts) =>
        val right = ts.count(_._1.endsWith(":"))
        if(right == 0)
          ts.foldLeft(e) { case (z, (o, a)) => AST.Ap(AST.Ident(o), Seq(z, a)) }
        else if(right == ts.length) {
          val e2 = ts.last._2
          val ts2 = ts.map(_._1).zip(e +: ts.map(_._2).init)
          ts2.foldRight(e2) { case ((o, a), z) => AST.Ap(AST.Ident(o), Seq(a, z)) }
        } else sys.error("Chained binary operators must have the same associativity")
    }
  }

  def expr[_: P]: P[AST.Expr] =
    P(  operatorEx(MaxPrecedence) ~ ("=" ~ operatorEx(MaxPrecedence)).?  ).map {
      case (e1, None) => e1
      case (e1, Some(e2)) => AST.Assignment(e1, e2)
    }

  def params[_: P](min: Int): P[Seq[String]] =
    P(  ("(" ~ param.rep(min = min, sep = ",") ~ ")")  )

  def param[_: P]: P[String] =
    P(  (ident | wildcard.map(_ => null) )  )

  def defReturn[_: P]: P[Seq[String]] =
    P(  params(1) | ident.map(Seq(_))  )

  def deriving[_ : P]: P[AST.Deriving] =
    P(  kw("deriving") ~/ "(" ~ ident.rep(0, sep=",") ~ ")" ).map(AST.Deriving)

  def cons[_: P]: P[AST.Cons] =
    P(  kw("cons") ~/ (operatorDef | namedCons) ~ (":" ~ ident).? ~ deriving.?  ).map(AST.Cons.tupled)

  def namedCons[_: P]: P[(String, Seq[String], Boolean)] =
    P(  ident ~ params(0).?.map(_.getOrElse(Nil))  ).map { case (n, as) => (n, as, false) }

  def operatorDef[_: P]: P[(String, Seq[String], Boolean)] =
    P(  param ~ anyOperator ~ param  ).map { case (a1, o, a2) => (o, Seq(a1, a2), true) }

  def definition[_: P]: P[AST.Def] =
    P(  kw("def") ~/ (operatorDef | namedDefinition) ~ (":" ~ defReturn).?.map(_.getOrElse(Nil)) ~ defRule.rep  ).map(AST.Def.tupled)

  def namedDefinition[_: P]: P[(String, Seq[String], Boolean)] =
    P(  ident ~ params(1)  ).map { case (n, as) => (n, as, false) }

  def defRule[_: P]: P[AST.DefRule] =
    P(  "|" ~ expr.rep(1, ",") ~ "=>" ~ expr.rep(1, sep = ",")  ).map(AST.DefRule.tupled)

  def matchStatement[_: P]: P[AST.Match] =
    P(  "match" ~ expr ~ "=>" ~ expr.rep(1, sep = ",")  ).map(AST.Match.tupled)

  def data[_: P]: P[AST.Data] =
    P(  kw("let") ~/ expr.rep(1, sep = ",") ).map(AST.Data)

  def unit[_: P]: P[Seq[AST.Statement]] =
    P(  Start ~ (cons | data | definition | matchStatement ).rep ~ End  )

  def parse(input: String): Seq[AST.Statement] =
    fastparse.parse(input, Parser.unit(_), verboseFailures = true).get.value

  def parse(file: Path): Seq[AST.Statement] =
    parse(new String(Files.readAllBytes(file), StandardCharsets.UTF_8))
}
