package de.szeiger.interact

import fastparse._

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

object AST {
  sealed trait Statement
  case class Cons(name: Ident, args: Seq[Ident], ret: Option[Ident], der: Option[Deriving], rules: Seq[ConsRule]) extends Statement {
    def arity = args.length
    def show: String = {
      val a = if(args.isEmpty) "" else args.map(_.s).mkString("(", ", ", ")")
      val r = if(ret.isEmpty) "" else s" . ${ret.get.show}"
      val d = if(der.isEmpty) "" else s" deriving ${der.get.show}"
      s"${name.s}$a$r$d"
    }
  }
  sealed trait ExprOrCut {
    def show: String
  }
  sealed trait Expr extends ExprOrCut {
    def target: Ident
    def args: Seq[Expr]
  }
  case class Ident(s: String) extends Expr {
    def show = s
    def target = this
    def args = Nil
  }
  case class Ap(target: Ident, args: Seq[Expr]) extends Expr {
    def show = s"${target.show}(${args.map(_.show).mkString(", ")})"
  }
  case class Cut(left: Expr, right: Expr) extends ExprOrCut {
    def show = s"${left.show} . ${right.show}"
  }
  case class Rule(cut: Cut, reduced: Seq[Cut]) extends Statement
  case class Data(free: Seq[Ident], cuts: Seq[Cut]) extends Statement {
    def show = cuts.map(_.show).mkString(", ")
  }
  case class Deriving(constructors: Seq[Ident]) {
    def show = constructors.map(_.show).mkString(", ")
  }
  case class ConsRule(rhs: Expr, reduced: Seq[Cut])
}

object Lexical {
  import NoWhitespace._

  val keywords = Set("cons", "rule", "let", "deriving", "cut")

  def identifier[_: P]: P[String] =
     P(  (letter|"_") ~ (letter | digit | "_").rep  ).!.filter(!keywords.contains(_))
  def kw[_: P](s: String) = P(  s ~ !(letter | digit | "_")  )
  def letter[_: P] = P( CharIn("a-z") | CharIn("A-Z") )
  def digit[_: P] = P( CharIn("0-9") )
  def churchLit[_: P] = P(  digit.rep(1).! ~ "'c"  ).map(_.toInt)
}

object Parser {
  import ScriptWhitespace._
  import Lexical._

  def ident[_: P]: P[AST.Ident] = identifier.map(AST.Ident(_))

  def church[_: P]: P[AST.Expr] = churchLit.map { i =>
    (1 to i).foldLeft(AST.Ident("Z"): AST.Expr) { case (z, _) => AST.Ap(AST.Ident("S"), z :: Nil) }
  }

  def app[_: P]: P[AST.Ap] =
    P(  ident ~ "(" ~ expr.rep(sep = ",") ~ ")"  ).map(AST.Ap.tupled)

  def simpleExpr[_: P]: P[AST.Expr] =
    P(  (app | ident | church)  )

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

  def paramsOpt[_: P]: P[Seq[AST.Ident]] =
    P(  ("(" ~ ident.rep(sep = ",") ~ ")").?  ).map(_.getOrElse(Nil))

  def deriving[_ : P]: P[AST.Deriving] =
    P(  kw("deriving") ~/ ident.rep(1, sep=",")  ).map(AST.Deriving(_))

  def consRule[_: P]: P[AST.ConsRule] =
    P(  kw("cut") ~/ expr ~ "=" ~ cutList  ).map(AST.ConsRule.tupled)

  def cons[_: P]: P[AST.Cons] =
    P(  kw("cons") ~/ ident ~ paramsOpt ~ ("." ~ ident).? ~ deriving.? ~ consRule.rep  ).map(AST.Cons.tupled)

  def rule[_: P]: P[AST.Rule] =
    P(  kw("rule") ~/ cut ~ "=" ~ cutList  ).map(AST.Rule.tupled)

  def data[_: P]: P[AST.Data] =
    P(  kw("let") ~/ ident.rep(1, sep = ",") ~ "=" ~ cutList ).map(AST.Data.tupled)

  def unit[_: P]: P[Seq[AST.Statement]] =
    P(  Start ~ (cons | rule | data).rep ~ End  )

  def parse(input: String): Seq[AST.Statement] =
    fastparse.parse(input, Parser.unit(_), verboseFailures = true).get.value

  def parse(file: Path): Seq[AST.Statement] =
    parse(new String(Files.readAllBytes(file), StandardCharsets.UTF_8))
}
