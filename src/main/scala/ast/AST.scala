package de.szeiger.interact.ast

import java.io.{OutputStreamWriter, PrintWriter}
import de.szeiger.interact.{ConvenientParserInput, MaybeColors}

import scala.collection.mutable.ArrayBuffer

sealed trait Node extends ShowableNode with Cloneable {
  override protected def clone(): this.type = super.clone().asInstanceOf[this.type]
  private var _pos: Position = Position.unknown
  def pos: Position = _pos
  def setPos(p: Position): this.type = {
    assert(_pos == p || _pos == Position.unknown, s"old pos ${_pos} != new pos $p")
    _pos = p
    this
  }
  def atPos(p: Position): this.type = {
    val e = (if(_pos == p || _pos == Position.unknown) this else clone()).asInstanceOf[this.type]
    e._pos = p
    e
  }
  protected[this] def simpleName: String = {
    val s = getClass.getName
    val i = s.lastIndexOf('.')
    if(i >= 0) s.drop(i+1) else s
  }
  def showNode: NodeInfo = {
    val ch = namedNodeChildren
    NodeInfo(simpleName, ch.msg,
      children = ch.iterator.map { case (n, s) => (s, n.showNode) }.toSeq,
      annot = if(pos.isDefined) pos.pretty else "")
  }
  def namedNodeChildren: NamedNodesBuilder = buildNodeChildren(namedNodes)
  def nodeChildren: Iterator[Node] = buildNodeChildren(new UnnamedNodesBuilder).iterator
  protected[this] def buildNodeChildren[N <: NodesBuilder](n: N): N = n
  protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder("")
}

sealed trait Statement extends Node

final case class CompilationUnit(statements: Vector[Statement]) extends Node {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += statements
}

final case class Cons(name: Ident, args: Vector[IdentOrWildcard], operator: Boolean, payloadType: PayloadType, embeddedId: Option[Ident], ret: Option[Ident], der: Option[Vector[Ident]]) extends Statement {
  def show: String = {
    val a = if(args.isEmpty) "" else args.map(_.show).mkString("(", ", ", ")")
    val p = if(payloadType.isDefined) s"[$payloadType${embeddedId.map(i => " "+i.show).getOrElse("")}]" else ""
    val r = if(ret.isEmpty) "" else s" . ${ret.get.show}"
    val d = if(der.isEmpty) "" else s" deriving ${der.get.map(_.show).mkString(", ")}"
    s"${name.show}$p$a$r$d"
  }
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (name, "name") += (args, "args") += (embeddedId, "embeddedId") += (ret, "ret") += (der.toSeq.flatten, "der")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder("")
}

sealed trait AnyExpr extends Node {
  def show: String
}

sealed trait EmbeddedExpr extends AnyExpr
sealed trait Expr extends AnyExpr {
  def allIdents: Iterator[Ident]
}
sealed trait IdentOrWildcard extends Expr {
  def isWildcard: Boolean
}

final case class IntLit(i: Int) extends EmbeddedExpr {
  def show = i.toString
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
}
final case class StringLit(s: String) extends EmbeddedExpr {
  def show = s"\"$s\""
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
}
final case class EmbeddedApply(methodQNIds: Vector[Ident], args: Vector[EmbeddedExpr]) extends EmbeddedExpr {
  lazy val methodQN = methodQNIds.map(_.s)
  def show = args.map(_.show).mkString(s"${methodQN.mkString(".")}(", ", ", ")")
  def className = methodQN.init.mkString(".")
  def methodName = methodQN.last
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (methodQNIds, "method") += (args, "args")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(methodQN.mkString("."))
}

final case class Ident(s: String) extends IdentOrWildcard with EmbeddedExpr {
  var sym: Symbol = Symbol.NoSymbol
  def show = s
  def allIdents: Iterator[Ident] = Iterator.single(this)
  override protected[this] def namedNodes: NamedNodesBuilder = {
    val msg = if(sym.isDefined) s"$s @ ${System.identityHashCode(sym)}" else s"$s @ <NoSymbol>"
    new NamedNodesBuilder(msg)
  }
  def isWildcard = false
}
final case class Wildcard() extends IdentOrWildcard {
  def show = "_"
  def allIdents: Iterator[Ident] = Iterator.empty
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
  def isWildcard = true
}
final case class Assignment(lhs: Expr, rhs: Expr) extends Expr {
  def show = s"${lhs.show} = ${rhs.show}"
  def allIdents = lhs.allIdents ++ rhs.allIdents
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (lhs, "lhs") += (rhs, "rhs")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
}
final case class Tuple(exprs: Vector[Expr]) extends Expr {
  def show = exprs.map(_.show).mkString("(", ", ", ")")
  def allIdents: Iterator[Ident] = exprs.iterator.flatMap(_.allIdents)
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += exprs
}
final case class Apply(target: Ident, embedded: Option[EmbeddedExpr], args: Vector[Expr]) extends Expr {
  def show = args.iterator.map(_.show).mkString(s"${target.show}${embedded.map(s => s"[${s.show}]").getOrElse("")}(", ", ", ")")
  def allIdents: Iterator[Ident] = Iterator.single(target) ++ args.iterator.flatMap(_.allIdents)
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (target, "target") += (embedded, "embedded") += (args, "args")
}
final case class ApplyCons(target: Ident, embedded: Option[EmbeddedExpr], args: Vector[Expr]) extends Expr {
  def show = args.iterator.map(_.show).mkString(s"<${target.show}>${embedded.map(s => s"[$s]").getOrElse("")}(", ", ", ")")
  def allIdents: Iterator[Ident] = Iterator.single(target) ++ args.iterator.flatMap(_.allIdents)
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (target, "target") += (embedded, "embedded") += (args, "args")
}

final case class Let(defs: Vector[Expr], embDefs: Vector[EmbeddedExpr]) extends Statement {
  def show = defs.map(_.show).mkString(", ")
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (defs, "defs") += (embDefs, "embDefs")
}

final case class Def(name: Ident, args: Vector[IdentOrWildcard], operator: Boolean, payloadType: PayloadType, embeddedId: Option[Ident], ret: Vector[IdentOrWildcard], rules: Vector[DefRule]) extends Statement {
  def show: String = {
    val a = if(args.isEmpty) "" else args.map(_.show).mkString("(", ", ", ")")
    val p = if(payloadType.isDefined) s"[$payloadType${embeddedId.map(i => " "+i.show).getOrElse("")}]" else ""
    val r = if(ret.isEmpty) "" else if(ret.length == 1) ret.head.show else ret.map(_.show).mkString("(", ", ", ")")
    s"${name.show}$p$a: $r"
  }
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (name, "name") += (args, "args") += (embeddedId, "embeddedId") += (ret, "ret") += (rules, "rules")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
}
final case class DefRule(on: Vector[Expr], reduced: Vector[Branch]) extends Node {
  def show = s"${on.map(_.show).mkString(", ")} ${Branch.show(reduced)}"
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (on, "on") += (reduced, "reduced")
}

final case class Match(on: Vector[Expr], reduced: Vector[Branch]) extends Statement {
  def show = s"${on.map(_.show).mkString(", ")} ${Branch.show(reduced)}"
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (on, "on") += (reduced, "reduced")
}

final case class Branch(cond: Option[EmbeddedExpr], embRed: Vector[EmbeddedExpr], reduced: Vector[Expr]) extends Node {
  def show(singular: Boolean) = {
    val es = embRed.map(e => s"[${e.show}]") ++ reduced.map(_.show)
    s"${cond.map(e => s"if [${e.show}] ").getOrElse(if(singular) "" else "else ")}=> ${es.mkString(", ")}"
  }
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (cond, "cond") += (embRed, "embRed") += (reduced, "reduced")
}
object Branch {
  def show(rs: Vector[Branch]) =
    if(rs.length == 1) rs.head.show(true) else rs.map(_.show(false)).mkString(" ")
}

sealed trait CheckedRule extends Statement {
  def show: String
  def sym1: Symbol
  def sym2: Symbol
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"${sym1.uniqueStr} . ${sym2.uniqueStr}")
}

final case class DerivedRule(sym1: Symbol, sym2: Symbol) extends CheckedRule {
  def show = s"$sym1 . $sym2 = <derived>"
}

final case class MatchRule(sym1: Symbol, sym2: Symbol, args1: Vector[Expr], args2: Vector[Expr],
    emb1: Option[EmbeddedExpr], emb2: Option[EmbeddedExpr], reduction: Vector[Branch]) extends CheckedRule {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) =
    n += (args1, "args1:") += (args2, "args2:") += (emb1, "emb1") += (emb2, "emb2") += (reduction, "red")
  def show: String = {
    def on(n: Symbol, e: Option[EmbeddedExpr], as: Vector[Expr]): String =
      s"$n${e.map(s => s"[${s.show}]").getOrElse("")}(${as.map(_.show).mkString(", ")})"
    s"match ${on(sym1, emb1, args1)} = ${on(sym2, emb2, args2)} ${Branch.show(reduction)}"
  }
}

object IdentOrAp {
  def unapply(e: Expr): Option[(Ident, Option[EmbeddedExpr], Vector[Expr])] = e match {
    case i: Ident => Some((i, None, Vector.empty))
    case Apply(i, emb, a) => Some((i, emb, a))
    case _ => None
  }
}
object IdentOrTuple {
  def unapply(e: Expr): Option[Vector[Expr]] = e match {
    case i: Ident => Some(Vector(i))
    case Tuple(es) => Some(es)
    case _ => None
  }
}

final class PayloadType(val value: Int) extends AnyVal {
  override def toString: String = value match {
    case 0 => "void"
    case 1 => "int"
    case 2 => "ref"
  }
  def isDefined: Boolean = value != 0
}
object PayloadType {
  final val VOID = new PayloadType(0)
  final val INT  = new PayloadType(1)
  final val REF  = new PayloadType(2)
  final val PAYLOAD_TYPES_COUNT = 3
}

final class Position(val offset: Int, val file: String, val input: ConvenientParserInput) {
  def pretty: String = {
    if(offset == -1) "unknown"
    else {
      val p = if(input == null) offset.toString else input.prettyIndex(offset)
      s"$file:$p"
    }
  }
  def isDefined: Boolean = this != Position.unknown
  override def toString: String = s"Position($pretty)"
}
object Position {
  val unknown = new Position(-1, null, null)
}

trait ShowableNode {
  def showNode: NodeInfo
}

object ShowableNode {
  import MaybeColors._

  def print(n: ShowableNode, out: PrintWriter = new PrintWriter(new OutputStreamWriter(System.out)), name: String = "", prefix: String = "", prefix1: String = null): Unit = {
    def f(n: NodeInfo, pf1: String, pf2: String, name: String, depth: Int): Unit = {
      val b = new StringBuilder(s"$pf1$cCyan")
      if(name.nonEmpty) b.append(s"$name: ")
      b.append(s"$cYellow${n.name}$cNormal ${n.msg}")
      if(n.annot.nonEmpty) b.append(s"  $cBlue${n.annot}$cNormal")
      out.println(b.result())
      val children = n.children.toIndexedSeq
      children.zipWithIndex.foreach { case ((name, n), idx) =>
        val (p1, p2) = if(idx == children.size-1) ("\u2514 ", "  ") else ("\u251c ", "\u2502 ")
        val (cp1, cp2) = if(depth % 2 == 0) (cBlue + p1, cBlue + p2) else (cGreen + p1, cGreen + p2)
        f(n, pf2 + cp1, pf2 + cp2, name, depth + 1)
      }
    }
    f(NodeInfo(n), if(prefix1 ne null) prefix1 else prefix, prefix, name, 0)
    out.flush()
  }
}

case class NodeInfo(name: String, msg: String = "", children: Iterable[(String, NodeInfo)] = Vector.empty, annot: String = "")

object NodeInfo {
  val empty = NodeInfo("null")
  def apply(s: ShowableNode): NodeInfo = if(s == null) empty else s.showNode
  def get(name: String, o: Option[ShowableNode]): Iterable[(String, NodeInfo)] = o match {
    case Some(n) => Vector(name -> NodeInfo(n))
    case None => Vector.empty
  }
  def get(ns: Iterable[ShowableNode], prefix: String = ""): Iterable[(String, NodeInfo)] = ns.zipWithIndex.map { case (n, i) =>
    s"$prefix$i" -> NodeInfo(n)
  }
}

sealed abstract class NodesBuilder {
  def += (n: Node): this.type
  def += (n: Node, s: String): this.type
  def += (n: Option[Node]): this.type
  def += (n: Option[Node], s: String): this.type
  def += (n: IterableOnce[Node]): this.type
  def += (n: IterableOnce[Node], prefix: String): this.type
}

final class NamedNodesBuilder(val msg: String) extends NodesBuilder {
  private[this] val buf = new ArrayBuffer[(Node, String)]()
  def += (n: Node): this.type = { buf += ((n, buf.length.toString)); this }
  def += (n: Node, s: String): this.type = { buf += ((n, s)); this }
  def += (n: Option[Node]): this.type = { n.foreach(+= _); this }
  def += (n: Option[Node], s: String): this.type = { n.foreach(n => buf += ((n, s))); this }
  def += (n: IterableOnce[Node]): this.type = { n.iterator.foreach(+= _); this }
  def += (n: IterableOnce[Node], prefix: String): this.type = {
    n.iterator.zipWithIndex.foreach { case (n, i) => buf += ((n, s"$prefix:$i")) }
    this
  }
  def iterator: Iterator[(Node, String)] = buf.iterator
}

final class UnnamedNodesBuilder extends NodesBuilder {
  private[this] val buf = new ArrayBuffer[Node]()
  def += (n: Node): this.type = { buf += n; this }
  def += (n: Node, s: String): this.type = { buf += n; this }
  def += (n: Option[Node]): this.type = { n.foreach(+= _); this }
  def += (n: Option[Node], s: String): this.type = { n.foreach(+= _); this }
  def += (n: IterableOnce[Node]): this.type = { n.iterator.foreach(+= _); this }
  def += (n: IterableOnce[Node], prefix: String): this.type = { n.iterator.foreach(+= _); this }
  def iterator: Iterator[Node] = buf.iterator
}
