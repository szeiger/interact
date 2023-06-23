package de.szeiger.interact

import fastparse._

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

object AST {
  sealed trait Statement
  case class Cons(name: String, args: Seq[String], operator: Boolean, embedded: Option[EmbeddedSpec], ret: Option[String], der: Option[Deriving]) extends Statement {
    def payloadType = embedded.map(_.payloadType).getOrElse(PayloadType.VOID)
    def show: String = {
      val a = if(args.isEmpty) "" else args.mkString("(", ", ", ")")
      val r = if(ret.isEmpty) "" else s" . ${ret.get}"
      val d = if(der.isEmpty) "" else s" deriving ${der.get.show}"
      s"$name$a$r$d"
    }
  }
  sealed trait AnyExpr
  sealed trait EmbeddedExpr extends AnyExpr {
    def show: String
  }
  case class EmbeddedIdent(s: String) extends EmbeddedExpr {
    def show = s
  }
  case class EmbeddedInt(i: Int) extends EmbeddedExpr {
    def show = i.toString
  }
  case class EmbeddedString(s: String) extends EmbeddedExpr {
    def show = s"\"$s\""
  }
  case class EmbeddedAp(methodQN: Seq[String], args: Seq[EmbeddedExpr]) extends EmbeddedExpr {
    def show = args.map(_.show).mkString(s"${methodQN.mkString(".")}(", ", ", ")")
    def className = methodQN.init.mkString(".")
    def methodName = methodQN.last
  }
  case class EmbeddedSpec(payloadType: Int, id: Option[String])
  case class Deriving(constructors: Seq[String]) {
    def show = constructors.mkString(", ")
  }
  trait Expr extends AnyExpr {
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
  case class Ap(target: Ident, embedded: Option[EmbeddedExpr], args: Seq[Expr]) extends Expr {
    def show = args.iterator.map(_.show).mkString(s"${target.show}${embedded.map(s => s"[${s.show}]").getOrElse("")}(", ", ", ")")
    def allIdents: Iterator[Ident] = Iterator.single(target) ++ args.iterator.flatMap(_.allIdents)
  }
  case class Data(defs: Seq[Expr], embDefs: Seq[EmbeddedExpr]) extends Statement {
    def show = defs.map(_.show).mkString(", ")
    var free: Seq[String] = _
  }
  case class Def(name: String, args: Seq[String], operator: Boolean, embedded: Option[EmbeddedSpec], ret: Seq[String], rules: Seq[DefRule]) extends Statement {
    def payloadType = embedded.map(_.payloadType).getOrElse(PayloadType.VOID)
    def embeddedId: Option[EmbeddedIdent] = embedded.flatMap(_.id).map(EmbeddedIdent)
    def show: String = {
      val a = if(args.isEmpty) "" else args.map(s => if(s == null) "_" else s).mkString("(", ", ", ")")
      val r = if(ret.isEmpty) "" else if(ret.length == 1) ret.head else ret.mkString("(", ", ", ")")
      s"$name$a: $r"
    }
  }
  case class DefRule(on: Seq[Expr], reduced: Seq[Reduction]) {
    def show = s"${on.map(_.show).mkString(", ")} ${Reduction.show(reduced)}"
  }
  case class Match(on: Expr, reds: Seq[Reduction]) extends Statement {
    def show = s"${on.show} ${Reduction.show(reds)}"
  }
  case class Reduction(cond: Option[EmbeddedExpr], embRed: Seq[EmbeddedExpr], reduced: Seq[Expr]) {
    def show(singular: Boolean) = s"${cond.map(e => s"if [${e.show}] ").getOrElse(if(singular) "" else "else ")}=> ${(embRed.map(_.show) ++ reduced.map(_.show)).mkString(", ")}"
  }
  object Reduction {
    def show(rs: Seq[Reduction]) =
      if(rs.length == 1) rs.head.show(true) else rs.map(_.show(false)).mkString(" ")
  }

  object IdentOrAp {
    def unapply(e: Expr): Option[(String, Option[EmbeddedExpr], Seq[Expr])] = e match {
      case Ident(s) => Some((s, None, Nil))
      case Ap(Ident(s), emb, a) => Some((s, emb, a))
      case _ => None
    }
  }
  object SimpleExprSpec {
    def unapply(e: Expr): Option[(String, Seq[Expr])] = e match {
      case Ident(s) => Some((s, Nil))
      case Ap(Ident(s), _, a) => Some((s, a))
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

  val reservedTokens = Set("cons", "let", "deriving", "def", "if", "else", "match", "_", ":", "=", "=>", "|")
  private val operatorStart = IndexedSeq(Set('*', '/', '%'), Set('+', '-'), Set(':'), Set('<', '>'), Set('=', '!'), Set('&'), Set('^'), Set('|'))
  private val operatorCont = operatorStart.iterator.flatten.toSet
  val MaxPrecedence = operatorStart.length-1

  def precedenceOf(s: String): Int =
    if(reservedTokens.contains(s) || !s.forall(operatorCont.contains)) -1
    else { val c = s.charAt(0); operatorStart.indexWhere(_.contains(c)) }
  def isRightAssoc(s: String): Boolean = s.endsWith(":")

  def ident[_: P]: P[String] =
     P(  (letter|"_") ~ (letter | digit | "_").rep  ).!.filter(!reservedTokens.contains(_))
  def kw[_: P](s: String) = P(  s ~ !(letter | digit | "_")  )
  def letter[_: P] = P( CharIn("a-z") | CharIn("A-Z") )
  def digit[_: P] = P( CharIn("0-9") )
  def churchLit[_: P] = P(  digit.rep(1).! ~ "'c"  ).map(_.toInt)
  def intLit[_: P] = P(  (("-").? ~ digit.rep(1)).!  ).map(_.toInt)

  def operator[_: P](precedence: Int): P[String] =
    P(  CharPred(operatorStart(precedence).contains) ~ CharPred(operatorCont.contains).rep  ).!.filter(s => !reservedTokens.contains(s))

  def anyOperator[_: P]: P[String] =
    P(  CharPred(operatorCont.contains).rep(1)  ).!.filter(s => !reservedTokens.contains(s))

  def stringLit[_: P]: P[String] = P(  "\"" ~ (stringChar | stringEscape).rep.! ~ "\""  )
  def stringChar[_: P]: P[Unit] = P( CharsWhile(!s"\\\n\"}".contains(_)) )
  def stringEscape[_: P]: P[Unit] = P( "\\" ~ AnyChar )
}

object EmbeddedSyntax {
  import ScriptWhitespace._
  import Lexical._

  def embeddedExpr[_: P]: P[AST.EmbeddedExpr] = P(  embeddedOperatorExpr(MaxPrecedence)  )

  def embeddedAp[_: P]: P[AST.EmbeddedAp] =
    P(  ident.rep(2, ".") ~ "(" ~ embeddedExpr.rep(0, ",") ~ ")"  ).map(AST.EmbeddedAp.tupled)

  def embeddedIdent[_: P]: P[AST.EmbeddedIdent] =
    P(  ident.map(AST.EmbeddedIdent)  )

  def bracketedEmbeddedExpr[_: P]: P[AST.EmbeddedExpr] =
    P(  "[" ~ embeddedExpr ~ "]"  )

  def simpleEmbeddedExpr[_: P]: P[AST.EmbeddedExpr] =
    P(  embeddedAp | embeddedIdent | intLit.map(AST.EmbeddedInt) | stringLit.map(AST.EmbeddedString) | ("(" ~ embeddedExpr ~ ")")  )

  def embeddedOperatorExpr[_: P](precedence: Int): P[AST.EmbeddedExpr] = {
    def next = if(precedence == 0) simpleEmbeddedExpr else embeddedOperatorExpr(precedence - 1)
    P(  next ~ (operator(precedence) ~ next).rep  ).map {
      case (e, Seq()) => e
      case (e, ts) =>
        val right = ts.count(_._1.endsWith(":"))
        if(right == 0)
          ts.foldLeft(e) { case (z, (o, a)) => AST.EmbeddedAp(Seq(o), Seq(z, a)) }
        else if(right == ts.length) {
          val e2 = ts.last._2
          val ts2 = ts.map(_._1).zip(e +: ts.map(_._2).init)
          ts2.foldRight(e2) { case ((o, a), z) => AST.EmbeddedAp(Seq(o), Seq(a, z)) }
        } else sys.error("Chained binary operators must have the same associativity")
    }
  }
}

object Parser {
  import ScriptWhitespace._
  import Lexical._
  import EmbeddedSyntax.bracketedEmbeddedExpr

  def identExpr[_: P]: P[AST.Ident] = ident.map(AST.Ident)

  def wildcard[_: P]: P[AST.Wildcard.type] = P("_").map(_ => AST.Wildcard)

  def church[_: P]: P[AST.Expr] = churchLit.map { i =>
    (1 to i).foldLeft(AST.Ident("Z"): AST.Expr) { case (z, _) => AST.Ap(AST.Ident("S"), None, z :: Nil) }
  }

  def appOrIdent[_: P]: P[AST.Expr] =
    P(  identExpr ~ bracketedEmbeddedExpr.? ~ ("(" ~ expr.rep(sep = ",") ~ ")").?  ).map { case (id, embO, argsO) =>
      if(embO.isDefined || argsO.isDefined) AST.Ap(id, embO, argsO.getOrElse(Nil)) else id
    }

  def tuple[_: P]: P[AST.Tuple] =
    P(  "(" ~ expr.rep(min = 0, sep = ",") ~ ")"  ).map(AST.Tuple)

  def simpleExpr[_: P]: P[AST.Expr] =
    P(  (appOrIdent | wildcard | church | tuple)  )

  def operatorEx[_: P](precedence: Int): P[AST.Expr] = {
    def next = if(precedence == 0) simpleExpr else operatorEx(precedence - 1)
    P(  next ~ (operator(precedence) ~ bracketedEmbeddedExpr.? ~ next).rep  ).map {
      case (e, Seq()) => e
      case (e, ts) =>
        val right = ts.count(_._1.endsWith(":"))
        if(right == 0)
          ts.foldLeft(e) { case (z, (o, oe, a)) => AST.Ap(AST.Ident(o), oe, Seq(z, a)) }
        else if(right == ts.length) {
          val e2 = ts.last._3
          val ts2 = ts.map(t => (t._1, t._2)).zip(e +: ts.map(_._3).init)
          ts2.foldRight(e2) { case (((o, oe), a), z) => AST.Ap(AST.Ident(o), oe, Seq(a, z)) }
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

  def embeddedSpecOpt[_: P]: P[Option[AST.EmbeddedSpec]] =
  P(  ("[" ~ ident ~ ident.? ~ "]"  ).?  ).map(_.map {
    case ("int", name) => AST.EmbeddedSpec(PayloadType.INT, name)
    case ("ref", name) => AST.EmbeddedSpec(PayloadType.REF, name)
    case (tpe, _) => sys.error(s"Illegal payload type: $tpe")
  })

  def cons[_: P]: P[AST.Cons] =
    P(  kw("cons") ~/ (operatorDef | namedCons) ~ (":" ~ ident).? ~ deriving.?  ).map(AST.Cons.tupled)

  def namedCons[_: P]: P[(String, Seq[String], Boolean, Option[AST.EmbeddedSpec])] =
    P(  ident ~ embeddedSpecOpt ~ params(0).?.map(_.getOrElse(Nil))  ).map { case (n, na, as) => (n, as, false, na) }

  def operatorDef[_: P]: P[(String, Seq[String], Boolean, Option[AST.EmbeddedSpec])] =
    P(  param ~ anyOperator ~ embeddedSpecOpt ~ param  ).map { case (a1, o, na, a2) => (o, Seq(a1, a2), true, na) }

  def definition[_: P]: P[AST.Def] =
    P(  kw("def") ~/ (operatorDef | namedDefinition) ~ (":" ~ defReturn).?.map(_.getOrElse(Nil)) ~ defRule.rep  ).map(AST.Def.tupled)

  def namedDefinition[_: P]: P[(String, Seq[String], Boolean, Option[AST.EmbeddedSpec])] =
    P(  ident ~ embeddedSpecOpt ~ params(1)  ).map { case (n, na, as) => (n, as, false, na) }

  def simpleReduction[_: P]: P[AST.Reduction] =
    P(  "=>" ~ (expr | bracketedEmbeddedExpr).rep(1, sep = ",")  ).map { es =>
      AST.Reduction(None, es.collect { case e: AST.EmbeddedExpr => e }, es.collect { case e: AST.Expr => e })
    }

  def conditionalReductions[_: P]: P[Seq[AST.Reduction]] =
    P(  ("if" ~ (bracketedEmbeddedExpr ~ simpleReduction).map { case (p, r) => r.copy(cond = Some(p))}).rep(1) ~
      "else" ~ simpleReduction
    ).map { case (rs, r) => rs :+ r }

  def reductions[_: P]: P[Seq[AST.Reduction]] =
    P(  conditionalReductions | simpleReduction.map(Seq(_))  )

  def condition[_: P]: P[AST.EmbeddedExpr] =
    P(  "if" ~ bracketedEmbeddedExpr  )

  def defRule[_: P]: P[AST.DefRule] =
    P(  "|" ~ expr.rep(1, ",") ~ reductions  ).map(AST.DefRule.tupled)

  def matchStatement[_: P]: P[AST.Match] =
    P(  "match" ~ expr ~ reductions  ).map(AST.Match.tupled)

  def data[_: P]: P[AST.Data] =
    P(  kw("let") ~/ (expr | bracketedEmbeddedExpr).rep(1, sep = ",") ).map { es =>
      AST.Data(es.collect { case e: AST.Expr => e }, es.collect { case e: AST.EmbeddedExpr => e })
    }

  def unit[_: P]: P[Seq[AST.Statement]] =
    P(  Start ~ (cons | data | definition | matchStatement ).rep ~ End  )

  def parse(input: String): Seq[AST.Statement] =
    fastparse.parse(input, Parser.unit(_), verboseFailures = true).get.value

  def parse(file: Path): Seq[AST.Statement] =
    parse(new String(Files.readAllBytes(file), StandardCharsets.UTF_8))
}
