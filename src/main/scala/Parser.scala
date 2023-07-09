package de.szeiger.interact

import fastparse._

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.collection.mutable
import de.szeiger.interact.ast._


import scala.collection.mutable.ArrayBuffer

object Lexical {
  val reservedTokens = Set("cons", "let", "deriving", "def", "if", "else", "match", "_", ":", "=", "=>", "|")
  private val operatorStart = IndexedSeq(Set('*', '/', '%'), Set('+', '-'), Set(':'), Set('<', '>'), Set('=', '!'), Set('&'), Set('^'), Set('|'))
  private val operatorCont = operatorStart.iterator.flatten.toSet
  val MaxPrecedence = operatorStart.length-1

  def precedenceOf(s: String): Int =
    if(reservedTokens.contains(s) || !s.forall(operatorCont.contains)) -1
    else { val c = s.charAt(0); operatorStart.indexWhere(_.contains(c)) }
  def isRightAssoc(s: String): Boolean = s.endsWith(":")
}

trait Lexical { this: Parser =>
  import NoWhitespace._
  import Lexical._

  def ident[_: P]: P[String] =
     P(  (letter|"_") ~ (letter | digit | "_").rep  ).!.filter(!reservedTokens.contains(_))
  def kw[_: P](s: String) = P(  s ~ !(letter | digit | "_")  )
  def letter[_: P] = P( CharIn("a-z") | CharIn("A-Z") )
  def digit[_: P] = P( CharIn("0-9") )
  def churchLit[_: P] = P(  digit.rep(1).! ~ "'c"  ).map(_.toInt)
  def intLit[_: P] = P(  (("-").? ~ digit.rep(1)).!  ).map(_.toInt)

  def operator[_: P](precedence: Int): P[String] =
    P(  CharPred(operatorStart(precedence).contains) ~ CharPred(operatorCont.contains).rep  ).!.filter(s => !reservedTokens.contains(s))

  def anyOperator[_: P]: P[Ident] =
    P(  positioned(CharPred(operatorCont.contains).rep(1).!.filter(s => !reservedTokens.contains(s)).map(Ident(_)))  )

  def stringLit[_: P]: P[String] = P(  "\"" ~ (stringChar | stringEscape).rep.! ~ "\""  )
  def stringChar[_: P]: P[Unit] = P( CharsWhile(!s"\\\n\"}".contains(_)) )
  def stringEscape[_: P]: P[Unit] = P( "\\" ~ AnyChar )

  def identExpr[_: P]: P[Ident] = positioned(ident.map(Ident))
}

trait EmbeddedSyntax { this: Parser =>
  import ScriptWhitespace._
  import Lexical._

  def embeddedExpr[_: P]: P[EmbeddedExpr] = P(  positioned(embeddedOperatorExpr(MaxPrecedence))  )

  def embeddedAp[_: P]: P[EmbeddedApply] =
    P(  identExpr.rep(2, ".") ~ "(" ~ embeddedExpr.rep(0, ",") ~ ")"  ).map(EmbeddedApply.tupled)

  def bracketedEmbeddedExpr[_: P]: P[EmbeddedExpr] =
    P(  "[" ~ embeddedExpr ~ "]"  )

  def simpleEmbeddedExpr[_: P]: P[EmbeddedExpr] =
    P(  embeddedAp | identExpr | intLit.map(IntLit) | stringLit.map(StringLit) | ("(" ~ embeddedExpr ~ ")")  )

  def operatorEmbeddedIdent[_: P](precedence: Int): P[Ident] = positioned(operator(precedence).map(Ident))

  def embeddedOperatorExpr[_: P](precedence: Int): P[EmbeddedExpr] = {
    def next = if(precedence == 0) positioned(simpleEmbeddedExpr) else embeddedOperatorExpr(precedence - 1)
    P(  next ~ (operatorEmbeddedIdent(precedence) ~ next).rep  ).map {
      case (e, Seq()) => e
      case (e, ts) =>
        val right = ts.count(_._1.s.endsWith(":"))
        if(right == 0)
          ts.foldLeft(e) { case (z, (o, a)) => EmbeddedApply(Seq(o), Seq(z, a)).setPos(o.pos) }
        else if(right == ts.length) {
          val e2 = ts.last._2
          val ts2 = ts.map(_._1).zip(e +: ts.map(_._2).init)
          ts2.foldRight(e2) { case ((o, a), z) => EmbeddedApply(Seq(o), Seq(a, z)).setPos(o.pos) }
        } else sys.error("Chained binary operators must have the same associativity")
    }
  }
}

trait Syntax { this: Parser =>
  import ScriptWhitespace._
  import Lexical._

  def wildcard[_: P]: P[Wildcard] = P("_").map(_ => Wildcard())

  def church[_: P]: P[Expr] = (pos ~ churchLit).map { case (p, i) =>
    (1 to i).foldLeft(Ident("Z").setPos(p): Expr) { case (z, _) => Apply(Ident("S").setPos(p), None, z :: Nil).setPos(p) }
  }

  def appOrIdent[_: P]: P[Expr] =
    P(
      positioned((identExpr ~ bracketedEmbeddedExpr.? ~ ("(" ~ expr.rep(sep = ",") ~ ")").?).map { case (id, embO, argsO) =>
        if(embO.isDefined || argsO.isDefined) Apply(id, embO, argsO.getOrElse(Nil)) else id
      })
    )

  def tuple[_: P]: P[Tuple] =
    P(  "(" ~ expr.rep(min = 0, sep = ",") ~ ")"  ).map(Tuple)

  def simpleExpr[_: P]: P[Expr] =
    P(  (appOrIdent | wildcard | church | tuple)  )

  def operatorIdent[_: P](precedence: Int): P[Ident] = positioned(operator(precedence).map(Ident(_)))

  def operatorEx[_: P](precedence: Int): P[Expr] = {
    def next = if(precedence == 0) positioned(simpleExpr) else operatorEx(precedence - 1)
    P(  next ~ (operatorIdent(precedence) ~ bracketedEmbeddedExpr.? ~ next).rep  ).map {
      case (e, Seq()) => e
      case (e, ts) =>
        val right = ts.count(_._1.s.endsWith(":"))
        if(right == 0)
          ts.foldLeft(e) { case (z, (o, oe, a)) => Apply(o, oe, Seq(z, a)).setPos(o.pos) }
        else if(right == ts.length) {
          val e2 = ts.last._3
          val ts2 = ts.map(t => (t._1, t._2)).zip(e +: ts.map(_._3).init)
          ts2.foldRight(e2) { case (((o, oe), a), z) => Apply(o, oe, Seq(a, z)).setPos(o.pos) }
        } else sys.error("Chained binary operators must have the same associativity")
    }
  }

  def expr[_: P]: P[Expr] =
    P(  positioned(operatorEx(MaxPrecedence)) ~ ("=" ~ positioned(operatorEx(MaxPrecedence))).?  ).map {
      case (e1, None) => e1
      case (e1, Some(e2)) => Assignment(e1, e2).setPos(e1.pos)
    }

  def params[_: P](min: Int): P[Seq[IdentOrWildcard]] =
    P(  ("(" ~ param.rep(min = min, sep = ",") ~ ")")  )

  def param[_: P]: P[IdentOrWildcard] =
    P(  positioned(identExpr | wildcard)  )

  def defReturn[_: P]: P[Seq[IdentOrWildcard]] =
    P(  params(1) | identExpr.map(Seq(_))  )

  def deriving[_ : P]: P[Seq[Ident]] =
    P(  kw("deriving") ~/ "(" ~ identExpr.rep(0, sep=",") ~ ")" )

  def embeddedSpecOpt[_: P]: P[(PayloadType, Option[Ident])] =
  P(  ("[" ~ ident ~ identExpr.? ~ "]"  ).?  ).map(_.map {
    case ("int", name) => (PayloadType.INT, name)
    case ("ref", name) => (PayloadType.REF, name)
    case (tpe, _) => sys.error(s"Illegal payload type: $tpe")
  }.getOrElse((PayloadType.VOID, None)))

  def cons[_: P]: P[Cons] =
    P(  kw("cons") ~/ (operatorDef | namedCons) ~ (":" ~ identExpr).? ~ deriving.?  ).map(Cons.tupled)

  def definition[_: P]: P[Def] =
    P(  kw("def") ~/ (operatorDef | namedDef) ~ (":" ~ defReturn).?.map(_.getOrElse(Nil)) ~ defRule.rep  ).map(Def.tupled)

  def namedCons[_: P]: P[(Ident, Seq[IdentOrWildcard], Boolean, PayloadType, Option[Ident])] =
    P(  identExpr ~ embeddedSpecOpt ~ params(0).?.map(_.getOrElse(Nil))  ).map { case (n, (pt, eid), as) => (n, as, false, pt, eid) }

  def operatorDef[_: P]: P[(Ident, Seq[IdentOrWildcard], Boolean, PayloadType, Option[Ident])] =
    P(  param ~ anyOperator ~ embeddedSpecOpt ~ param  ).map { case (a1, o, (pt, eid), a2) => (o, Seq(a1, a2), true, pt, eid) }

  def namedDef[_: P]: P[(Ident, Seq[IdentOrWildcard], Boolean, PayloadType, Option[Ident])] =
    P(  identExpr ~ embeddedSpecOpt ~ params(1)  ).map { case (n, (pt, eid), as) => (n, as, false, pt, eid) }

  def anyExpr[_ : P]: P[Either[EmbeddedExpr, Expr]] =
    P(  bracketedEmbeddedExpr.map(Left(_)) | expr.map(Right(_))  )

  def simpleReduction[_: P]: P[Branch] = P(
    positioned("=>" ~ anyExpr.rep(1, sep = ",").map { es =>
      val embRed = es.collect { case Left(e) => e }
      val red = es.collect { case Right(e) => e }
      Branch(None, embRed, red)
    })
  )

  def conditionalReductions[_: P]: P[Seq[Branch]] =
    P(  ("if" ~ (bracketedEmbeddedExpr ~ simpleReduction).map { case (p, r) => r.copy(cond = Some(p)).setPos(r.pos)}).rep(1) ~
      "else" ~ simpleReduction
    ).map { case (rs, r) => rs :+ r }

  def reductions[_: P]: P[Seq[Branch]] =
    P(  conditionalReductions | simpleReduction.map(Seq(_))  )

  def condition[_: P]: P[EmbeddedExpr] =
    P(  "if" ~ bracketedEmbeddedExpr  )

  def defRule[_: P]: P[DefRule] =
    P(  positioned(("|" ~ expr.rep(1, ",") ~ reductions).map(DefRule.tupled))  )

  def matchStatement[_: P]: P[Match] =
    P(  "match" ~ expr ~ reductions  ).map(Match.tupled)

  def data[_: P]: P[Let] =
    P(  kw("let") ~/ (expr.map(_ -> true) | bracketedEmbeddedExpr.map(_ -> false)).rep(1, sep = ",") ).map { es =>
      Let(es.collect { case (e: Expr, true) => e }, es.collect { case (e: EmbeddedExpr, false) => e })
    }

  def unit[_: P]: P[CompilationUnit] =
    P(  Start ~ pos ~ positioned(cons | data | definition | matchStatement ).rep ~ End  ).map { case (p, es) => CompilationUnit(es).setPos(p) }
}

class Parser(file: String, indexed: ConvenientParserInput) extends Lexical with EmbeddedSyntax with Syntax {
  import NoWhitespace._

  private[this] val positions = mutable.LongMap.empty[Position]

  def pos[_: P]: P[Position] = Index.map { offset => positions.getOrElseUpdate(offset, new Position(offset, file, indexed)) }
  def positioned[T <: Node, _: P](n: => P[T]): P[T] = P(  (pos ~ n)  ).map { case (p, e) =>
    if(!e.pos.isDefined) e.setPos(p) else e
  }
}

object Parser {
  def parse(input: String, file: String = "<input>"): CompilationUnit = {
    val in = new ConvenientParserInput(input)
    val p = new Parser(file, in)
    fastparse.parse(in, p.unit(_), verboseFailures = true).get.value
  }

  def parse(file: Path): CompilationUnit =
    parse(new String(Files.readAllBytes(file), StandardCharsets.UTF_8), file.toString)
}

class ConvenientParserInput(val data: String) extends ParserInput {
  def apply(index: Int): Char = data.charAt(index)
  def dropBuffer(index: Int): Unit = ()
  def slice(from: Int, until: Int): String = data.slice(from, until)
  def length: Int = data.length
  def innerLength: Int = length
  def isReachable(index: Int): Boolean = index < length
  def checkTraceable(): Unit = ()

  private[this] lazy val lineBreaks = {
    val b = ArrayBuffer.empty[Int]
    for(i <- data.indices)
      if(data.charAt(i) == '\n') b += i
    b
  }

  def find(idx: Int): (Int, Int) = {
    val line = lineBreaks.indexWhere(_ > idx) match {
      case -1 => lineBreaks.length
      case n => n
    }
    val col = if(line == 0) idx else idx - lineBreaks(line-1) - 1
    (line, col)
  }

  def prettyIndex(idx: Int): String = {
    val (line, pos) = find(idx)
    s"${line+1}:${pos+1}"
  }

  def getLine(line: Int): String = {
    val start = if(line == 0) 0 else lineBreaks(line-1)
    val end = if(line == lineBreaks.length) data.length else lineBreaks(line)
    data.substring(start, end).dropWhile(c => c == '\r' || c == '\n')
  }

  def getCaret(col: Int): String = (" " * col) + "^"
}
