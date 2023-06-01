package de.szeiger.interact

import fastparse._

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

object AST {
  sealed trait Statement
  case class Cons(name: String, args: Seq[String], ret: Option[String], der: Option[Deriving], rules: Seq[ConsRule]) extends Statement {
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
  case class ConsRule(rhs: Expr, reduced: Seq[Cut])
  sealed trait ExprOrCut {
    def show: String
  }
  sealed trait DefExpr {
    def show: String
  }
  sealed trait Expr extends ExprOrCut with DefExpr {
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
  case class Assignment(lhs: Expr, rhs: Expr) extends DefExpr {
    def show = s"${lhs.show} = ${rhs.show}"
  }
  case class Tuple(exprs: Seq[Expr]) extends Expr {
    def show = exprs.map(_.show).mkString("(", ", ", ")")
    def allIdents: Iterator[Ident] = exprs.iterator.flatMap(_.allIdents)
  }
  case class Ap(target: Ident, args: Seq[Expr]) extends Expr {
    def show = args.iterator.map(_.show).mkString(s"${target.show}(", ", ", ")")
    def allIdents: Iterator[Ident] = Iterator.single(target) ++ args.iterator.flatMap(_.allIdents)
  }
  case class Cut(left: Expr, right: Expr) extends ExprOrCut {
    def show = s"${left.show} . ${right.show}"
  }
  case class Rule(cut: Cut, reduced: Seq[Cut], derived: Boolean) extends Statement
  case class Data(free: Seq[String], cuts: Seq[Cut]) extends Statement {
    def show = cuts.map(_.show).mkString(", ")
  }
  case class Def(name: String, args: Seq[String], ret: Seq[String], rules: Seq[DefRule]) extends Statement {
    def show: String = {
      val a = if(args.isEmpty) "" else args.map(s => if(s == null) "_" else s).mkString("(", ", ", ")")
      val r = if(ret.isEmpty) "" else if(ret.length == 1) ret.head else ret.mkString("(", ", ", ")")
      s"$name$a: $r"
    }
  }
  case class DefRule(on: DefExpr, reduced: Seq[DefExpr])

  object IdentOrAp {
    def unapply(e: Expr): Option[(String, Seq[Expr])] = e match {
      case Ident(s) => Some((s, Nil))
      case Ap(Ident(s), a) => Some((s, a))
      case _ => None
    }
  }
  object ExprSpec {
    def unapply(e: Expr): Option[(String, Seq[Expr])] = e match {
      case Ident(s) => Some((s, Nil))
      case Ap(Ident(s), a) => Some((s, a))
      case Wildcard => Some((null, Nil))
      case Tuple(args) => Some((null, args))
    }
  }
}

object Lexical {
  import NoWhitespace._

  val keywords = Set("cons", "rule", "let", "deriving", "cut", "def", "_")

  def ident[_: P]: P[String] =
     P(  (letter|"_") ~ (letter | digit | "_").rep  ).!.filter(!keywords.contains(_))
  def kw[_: P](s: String) = P(  s ~ !(letter | digit | "_")  )
  def letter[_: P] = P( CharIn("a-z") | CharIn("A-Z") )
  def digit[_: P] = P( CharIn("0-9") )
  def churchLit[_: P] = P(  digit.rep(1).! ~ "'c"  ).map(_.toInt)
}

object Parser {
  import ScriptWhitespace._
  import Lexical._

  def identExpr[_: P]: P[AST.Ident] = ident.map(AST.Ident(_))

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

  def expr[_: P]: P[AST.Expr] =
    P(  simpleExpr.rep(1, "::")  ).map {
      case Seq(e) => e
      case es => es.foldRight(null: AST.Expr) {
        case (e, null) => e
        case (e, z) => AST.Ap(AST.Ident("Cons"), Seq(e, z))
      }
    }

  def cut[_: P]: P[AST.Cut] =
    P(expr ~ "." ~ expr).map(AST.Cut.tupled)

  def cutList[_: P]: P[Seq[AST.Cut]] =
    P(  cut.rep(min = 1, sep = ",") | P("()").map(_ => Nil)  )

  def params[_: P](min: Int): P[Seq[String]] =
    P(  ("(" ~ (ident | wildcard.map(_ => null) ).rep(min = min, sep = ",") ~ ")")  )

  def consParamsOpt[_: P]: P[Seq[String]] =
    P(  params(0).?  ).map(_.getOrElse(Nil))

  def defReturn[_: P]: P[Seq[String]] =
    P(  params(1) | ident.map(Seq(_))  )

  def deriving[_ : P]: P[AST.Deriving] =
    P(  kw("deriving") ~/ ident.rep(1, sep=",")  ).map(AST.Deriving(_))

  def consRule[_: P]: P[AST.ConsRule] =
    P(  kw("cut") ~/ expr ~ "=" ~ cutList  ).map(AST.ConsRule.tupled)

  def cons[_: P]: P[AST.Cons] =
    P(  kw("cons") ~/ ident ~ consParamsOpt ~ ("." ~ ident).? ~ deriving.? ~ consRule.rep  ).map(AST.Cons.tupled)

  def definition[_: P]: P[AST.Def] =
    P(  kw("def") ~/ ident ~ params(1) ~ (":" ~ defReturn).?.map(_.getOrElse(Nil)) ~ defRule.rep  ).map(AST.Def.tupled)

  def defRule[_: P]: P[AST.DefRule] =
    P(  "|" ~ defExpr ~ "=>" ~ defExpr.rep(1, sep = ",")  ).map(AST.DefRule.tupled)

  def defExpr[_: P]: P[AST.DefExpr] =
    P(  expr ~ ("=" ~ expr).?  ).map {
      case (e1, None) => e1
      case (e1, Some(e2)) => AST.Assignment(e1, e2)
    }

  def rule[_: P]: P[AST.Rule] =
    P(  kw("rule") ~/ cut ~ "=" ~ cutList  ).map { case (c, e) => AST.Rule(c, e, false) }

  def data[_: P]: P[AST.Data] =
    P(  kw("let") ~/ ident.rep(1, sep = ",") ~ "=" ~ cutList ).map(AST.Data.tupled)

  def unit[_: P]: P[Seq[AST.Statement]] =
    P(  Start ~ (cons | rule | data | definition ).rep ~ End  )

  def parse(input: String): Seq[AST.Statement] =
    fastparse.parse(input, Parser.unit(_), verboseFailures = true).get.value

  def parse(file: Path): Seq[AST.Statement] =
    parse(new String(Files.readAllBytes(file), StandardCharsets.UTF_8))
}
