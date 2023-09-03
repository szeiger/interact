package de.szeiger.interact

import fastparse._

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.collection.mutable
import de.szeiger.interact.ast._


import scala.collection.mutable.ArrayBuffer

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
  def natLit[_: P] = P(  digit.rep(1).! ~ "n"  ).map(_.toInt)
  def intLit[_: P] = P(  (("-").? ~ digit.rep(1)).!  ).map(_.toInt)

  def operator[_: P](precedence: Int): P[String] =
    P(  CharPred(operatorStart(precedence).contains) ~ CharPred(operatorCont.contains).rep  ).!.filter(s => !reservedTokens.contains(s))

  def anyOperator[_: P]: P[Ident] =
    P(  CharPred(operatorCont.contains).rep(1).!.filter(s => !reservedTokens.contains(s)).map(Ident(_))  )

  def stringLit[_: P]: P[String] = P(  "\"" ~ (stringChar | stringEscape).rep.! ~ "\""  )
  def stringChar[_: P]: P[Unit] = P( CharsWhile(!s"\\\n\"}".contains(_)) )
  def stringEscape[_: P]: P[Unit] = P( "\\" ~ AnyChar )

  def comment[$: P] = P( "#" ~ CharsWhile(_ != '\n', 0) )
  def whitespace[$: P](indent: Int) = P(
    CharsWhile(_ == ' ', 0) ~ (CharsWhile(_ == ' ', 0) ~ comment.? ~ "\r".? ~ "\n" ~ " ".rep(indent)).rep(0)
  )
}

trait EmbeddedSyntax { this: Parser =>
  import Lexical._

  def identExpr[_: P]: P[Ident] = positioned(ident.map(Ident))

  def embeddedExpr[_: P]: P[EmbeddedExpr] =
    P(  positioned(embeddedOperatorExpr(MaxPrecedence))  )

  def embeddedAssignment[_: P]: P[EmbeddedAssignment] =
    P(  positioned((identExpr ~ "=" ~ embeddedExpr).map { case (id, ee) => EmbeddedAssignment(id, ee) })  )

  def embeddedExprOrAssignment[_: P]: P[EmbeddedExpr] =
    P(  embeddedAssignment | embeddedExpr  )

  def embeddedAp[_: P]: P[EmbeddedApply] =
    P(  identExpr.rep(1, ".").map(_.toVector) ~ "(" ~ embeddedExpr.rep(0, ",").map(_.toVector) ~ ")"  ).map { case (method, args) =>
      EmbeddedApply(method, args, false, EmbeddedType.Unknown)
    }

  def bracketedEmbeddedExpr[_: P]: P[EmbeddedExpr] =
    P(  "[" ~ embeddedExprOrAssignment ~ "]"  )

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
          ts.foldLeft(e) { case (z, (o, a)) => EmbeddedApply(Vector(o), Vector(z, a), true, EmbeddedType.Unknown).setPos(o.pos) }
        else if(right == ts.length) {
          val e2 = ts.last._2
          val ts2 = ts.map(_._1).zip(e +: ts.map(_._2).init)
          ts2.foldRight(e2) { case ((o, a), z) => EmbeddedApply(Vector(o), Vector(a, z), true, EmbeddedType.Unknown).setPos(o.pos) }
        } else sys.error("Chained binary operators must have the same associativity")
    }
  }
}

trait Syntax { this: Parser =>
  import Lexical._

  def wildcard[_: P]: P[Wildcard] = P("_").map(_ => Wildcard())

  def nat[_: P]: P[Expr] = P(  positioned(natLit.map(NatLit))  )

  def appOrIdent[_: P]: P[Expr] =
    P(
      positioned((identExpr ~ bracketedEmbeddedExpr.? ~ ("(" ~ expr.rep(sep = ",") ~ ")").?).map { case (id, embO, argsO) =>
        if(embO.isDefined || argsO.isDefined) Apply(id, embO, argsO.getOrElse(Vector.empty).toVector) else id
      })
    )

  def tuple[_: P]: P[Tuple] =
    P(  "(" ~ expr.rep(min = 0, sep = ",").map(_.toVector) ~ ")"  ).map(Tuple)

  def simpleExpr[_: P]: P[Expr] =
    P(  (appOrIdent | wildcard | nat | tuple)  )

  def operatorIdent[_: P](precedence: Int): P[Ident] = positioned(operator(precedence).map(Ident(_)))

  def operatorEx[_: P](precedence: Int): P[Expr] = {
    def next = if(precedence == 0) positioned(simpleExpr) else operatorEx(precedence - 1)
    P(  next ~ (operatorIdent(precedence) ~ bracketedEmbeddedExpr.? ~ next).rep  ).map {
      case (e, Seq()) => e
      case (e, ts) =>
        val right = ts.count(_._1.s.endsWith(":"))
        if(right == 0)
          ts.foldLeft(e) { case (z, (o, oe, a)) => Apply(o, oe, Vector(z, a)).setPos(o.pos) }
        else if(right == ts.length) {
          val e2 = ts.last._3
          val ts2 = ts.map(t => (t._1, t._2)).zip(e +: ts.map(_._3).init)
          ts2.foldRight(e2) { case (((o, oe), a), z) => Apply(o, oe, Vector(a, z)).setPos(o.pos) }
        } else sys.error("Chained binary operators must have the same associativity")
    }
  }

  def expr[_: P]: P[Expr] =
    P(  positioned(operatorEx(MaxPrecedence)) ~ ("=" ~ positioned(operatorEx(MaxPrecedence))).?  ).map {
      case (e1, None) => e1
      case (e1, Some(e2)) => Assignment(e1, e2).setPos(e1.pos)
    }

  def params[_: P](min: Int): P[Vector[IdentOrWildcard]] =
    P(  ("(" ~ param.rep(min = min, sep = ",").map(_.toVector) ~ ")")  )

  def param[_: P]: P[IdentOrWildcard] =
    P(  positioned(identExpr | wildcard)  )

  def defReturn[_: P]: P[Vector[IdentOrWildcard]] =
    P(  params(1) | identExpr.map(Vector(_))  )

  def deriving[_ : P]: P[Vector[Ident]] =
    P(  kw("deriving") ~/ "(" ~ identExpr.rep(0, sep=",").map(_.toVector) ~ ")" )

  def payloadType[_: P]: P[PayloadType] =
    P(ident).map {
      case "int" => (PayloadType.INT)
      case "ref" => (PayloadType.REF)
      case "label" => (PayloadType.LABEL)
      case tpe => sys.error(s"Illegal payload type: $tpe")
    }

  def embeddedSpecOpt[_: P]: P[(PayloadType, Option[Ident])] =
  P(  ("[" ~ payloadType ~ identExpr.? ~ "]"  ).?  ).map(_.getOrElse((PayloadType.VOID, None)))

  def cons[_: P]: P[Cons] =
    P(  kw("cons") ~/ (operatorDef | namedCons) ~ ("=" ~ identExpr).? ~ deriving.?  ).map(Cons.tupled)

  def definition[_: P]: P[Def] =
    P(  kw("def") ~/ (operatorDef | namedDef) ~ ("=" ~ defReturn).?.map(_.getOrElse(Vector.empty)) ~ defRule.rep.map(_.toVector)  ).map(Def.tupled)

  def namedCons[_: P]: P[(Ident, Vector[IdentOrWildcard], Boolean, PayloadType, Option[Ident])] =
    P(  identExpr ~ embeddedSpecOpt ~ params(0).?.map(_.getOrElse(Vector.empty))  ).map { case (n, (pt, eid), as) => (n, as, false, pt, eid) }

  def operatorDef[_: P]: P[(Ident, Vector[IdentOrWildcard], Boolean, PayloadType, Option[Ident])] =
    P(  param ~ positioned(anyOperator) ~ embeddedSpecOpt ~ param  ).map { case (a1, o, (pt, eid), a2) => (o, Vector(a1, a2), true, pt, eid) }

  def namedDef[_: P]: P[(Ident, Vector[IdentOrWildcard], Boolean, PayloadType, Option[Ident])] =
    P(  identExpr ~ embeddedSpecOpt ~ params(1)  ).map { case (n, (pt, eid), as) => (n, as, false, pt, eid) }

  def anyExpr[_ : P]: P[Either[EmbeddedExpr, Expr]] =
    P(  bracketedEmbeddedExpr.map(Left(_)) | expr.map(Right(_))  )

  def anyExprs[_: P]: P[Vector[Either[EmbeddedExpr, Expr]]] =
    P(  anyExpr.rep(1, sep = ";").map(_.toVector) ~ ";".?  )

  def anyExprBlock[_: P]: P[(Vector[Expr], Vector[EmbeddedExpr])] =
    P(  pos.flatMapX(p => forIndent(p.column).anyExprBlock2)  )

  def anyExprBlock2[_: P]: P[(Vector[Expr], Vector[EmbeddedExpr])] =
    P(  (forIndent(indent+1).anyExprs).rep(1)  ).map { es =>
      (es.iterator.flatten.collect { case Right(e) => e }.toVector, es.iterator.flatten.collect { case Left(e) => e }.toVector)
    }

  def simpleReduction[_: P]: P[Branch] =
    P(  positioned("=>" ~ anyExprBlock.map { case (es, ees) => Branch(None, ees, es) })  )

  def conditionalReductions[_: P]: P[Vector[Branch]] =
    P(  ("if" ~ (bracketedEmbeddedExpr ~ simpleReduction).map { case (p, r) => r.copy(cond = Some(p)).setPos(r.pos)}).rep(1).map(_.toVector) ~
      "else" ~ simpleReduction
    ).map { case (rs, r) => rs :+ r }

  def reductions[_: P]: P[Vector[Branch]] =
    P(  conditionalReductions | simpleReduction.map(Vector(_))  )

  def condition[_: P]: P[EmbeddedExpr] =
    P(  "if" ~ bracketedEmbeddedExpr  )

  def defRule[_: P]: P[DefRule] =
    P(  positioned(("|" ~ expr.rep(1, ",").map(_.toVector) ~ reductions).map(DefRule.tupled))  )

  def matchStatement[_: P]: P[Match] =
    P(  "match" ~ expr ~ reductions  ).map { case (on, red) => Match(Vector(on), red) }

  def let[_: P]: P[Let] =
    P(  kw("let") ~/ anyExprBlock  ).map(Let.tupled)

  def unit[_: P]: P[CompilationUnit] =
    P(  Start ~ pos ~ positioned(cons | let | definition | matchStatement ).rep ~ End  ).map { case (p, es) => CompilationUnit(es.toVector).setPos(p) }
}

class Parser(file: String, indexed: ConvenientParserInput, val indent: Int) extends EmbeddedSyntax with Syntax {
  implicit val whitespace: fastparse.Whitespace =
    (ctx: P[_]) => Lexical.whitespace(indent)(ctx)

  private[this] val positions = mutable.LongMap.empty[Position]

  def pos[_: P]: P[Position] = Index.map { offset => positions.getOrElseUpdate(offset, new Position(offset, file, indexed)) }

  def positioned[T <: Node, _: P](n: => P[T]): P[T] =
    P(  (pos ~~ n)  ).map { case (p, e) => if(!e.pos.isDefined) e.setPos(p) else e }

  def forIndent(i: Int): Parser = new Parser(file, indexed, i)
}

object Parser {
  def parse(input: String, file: String = "<input>"): CompilationUnit = {
    val in = new ConvenientParserInput(input)
    val p = new Parser(file, in, 0)
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
