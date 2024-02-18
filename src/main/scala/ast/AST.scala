package de.szeiger.interact.ast

import java.io.{OutputStreamWriter, PrintWriter}
import de.szeiger.interact.{ConvenientParserInput, MaybeColors, Runtime}

import scala.collection.mutable.ArrayBuffer

trait Node extends ShowableNode with Cloneable {
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

trait Statement extends Node

final case class CompilationUnit(statements: Vector[Statement]) extends Node {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += statements
  def copy(statements: Vector[Statement] = statements): CompilationUnit = CompilationUnit(statements).setPos(pos)
}

final case class Cons(name: Ident, args: Vector[IdentOrWildcard], operator: Boolean, payloadType: PayloadType, embeddedId: Option[Ident], ret: Option[Ident], der: Option[Vector[Ident]]) extends Statement {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (name, "name") += (args, "args") += (embeddedId, "embeddedId") += (ret, "ret") += (der.toSeq.flatten, "der")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"operator=$operator, payloadType=$payloadType")
  def copy(name: Ident = name, args: Vector[IdentOrWildcard] = args, operator: Boolean = operator, payloadType: PayloadType = payloadType, embeddedId: Option[Ident] = embeddedId, ret: Option[Ident] = ret, der: Option[Vector[Ident]] = der): Cons =
    Cons(name, args, operator, payloadType, embeddedId, ret, der).setPos(pos)
}

sealed trait AnyExpr extends Node

sealed trait EmbeddedExpr extends AnyExpr
sealed trait Expr extends AnyExpr
sealed trait IdentOrWildcard extends Expr {
  def isWildcard: Boolean
}

final case class EmbeddedAssignment(lhs: Ident, rhs: EmbeddedExpr) extends EmbeddedExpr {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (lhs, "lhs") += (rhs, "rhs")
  def copy(lhs: Ident = lhs, rhs: EmbeddedExpr = rhs): EmbeddedAssignment = EmbeddedAssignment(lhs, rhs).setPos(pos)
}
final case class CreateLabels(base: Symbol, labels: Vector[Symbol]) extends EmbeddedExpr {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"<createLabels $base -> ${labels.mkString(", ")}>")
  def copy(base: Symbol = base, labels: Vector[Symbol] = labels): CreateLabels = CreateLabels(base, labels).setPos(pos)
}
final case class IntLit(i: Int) extends EmbeddedExpr {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(i.toString)
  def copy(i: Int = i): IntLit = IntLit(i).setPos(pos)
}
final case class StringLit(s: String) extends EmbeddedExpr {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"\"$s\"")
  def copy(s: String = s): StringLit = StringLit(s).setPos(pos)
}
final case class EmbeddedApply(methodQNIds: Vector[Ident], args: Vector[EmbeddedExpr], op: Boolean, embTp: EmbeddedType) extends EmbeddedExpr {
  lazy val methodQN = methodQNIds.map(_.s)
  def className = if(methodQN.length ==1) Runtime.getClass.getName else methodQN.init.mkString(".")
  def methodName = methodQN.last
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (methodQNIds, "method") += (args, "args")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"${methodQN.mkString(".")}, op=$op, embTp=$embTp")
  def copy(methodQNIds: Vector[Ident] = methodQNIds, args: Vector[EmbeddedExpr] = args, op: Boolean = op, embTp: EmbeddedType = embTp): EmbeddedApply =
    EmbeddedApply(methodQNIds, args, op, embTp).setPos(pos)
}

final case class Ident(s: String) extends IdentOrWildcard with EmbeddedExpr {
  var sym: Symbol = Symbol.NoSymbol
  def setSym(s: Symbol): this.type = { sym = s; this }
  override protected[this] def namedNodes: NamedNodesBuilder = {
    val msg = if(sym.isDefined) s"$s @ ${sym.show}" else s"$s @ <NoSymbol>"
    new NamedNodesBuilder(msg)
  }
  def isWildcard = false
  def copy(s: String = s): Ident = Ident(s).setPos(pos)
}
final case class Wildcard() extends IdentOrWildcard {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder("_")
  def isWildcard = true
  def copy(): Wildcard = Wildcard().setPos(pos)
}
final case class Assignment(lhs: Expr, rhs: Expr) extends Expr {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (lhs, "lhs") += (rhs, "rhs")
  def copy(lhs: Expr = lhs, rhs: Expr = rhs): Assignment = Assignment(lhs, rhs).setPos(pos)
}
final case class Tuple(exprs: Vector[Expr]) extends Expr {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += exprs
  def copy(exprs: Vector[Expr] = exprs): Tuple = Tuple(exprs).setPos(pos)
}
sealed trait AnyApply extends Expr {
  def target: Ident
  def embedded: Option[EmbeddedExpr]
  def args: Vector[Expr]
  def copy(target: Ident = target, embedded: Option[EmbeddedExpr] = embedded, args: Vector[Expr] = args): AnyApply
}
object AnyApply {
  def unapply(e: AnyApply): Some[(Ident, Option[EmbeddedExpr], Vector[Expr], Boolean)] = e match {
    case Apply(t, e, as) => Some((t, e, as, false))
    case ApplyCons(t, e, as) => Some((t, e, as, true))
  }
}

final case class Apply(target: Ident, embedded: Option[EmbeddedExpr], args: Vector[Expr]) extends AnyApply {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (target, "target") += (embedded, "embedded") += (args, "args")
  def copy(target: Ident = target, embedded: Option[EmbeddedExpr] = embedded, args: Vector[Expr] = args) = Apply(target, embedded, args).setPos(pos)
}
final case class ApplyCons(target: Ident, embedded: Option[EmbeddedExpr], args: Vector[Expr]) extends AnyApply {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (target, "target") += (embedded, "embedded") += (args, "args")
  def copy(target: Ident = target, embedded: Option[EmbeddedExpr] = embedded, args: Vector[Expr] = args) = ApplyCons(target, embedded, args).setPos(pos)
}
final case class NatLit(i: Int) extends Expr {
  var sSym, zSym: Symbol = Symbol.NoSymbol
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"${i}n")
  def expand: Expr = {
    assert(sSym.isCons)
    assert(zSym.isCons)
    val z = Apply(Ident("Z").setPos(pos).setSym(zSym), None, Vector.empty).setPos(pos)
    (1 to i).foldLeft(z) { case (z, _) => Apply(Ident("S").setPos(pos).setSym(sSym), None, Vector(z)).setPos(pos) }
  }
  def copy(i: Int = i): NatLit = NatLit(i).setPos(pos)
}

final case class Let(defs: Vector[Expr], embDefs: Vector[EmbeddedExpr], free: Vector[Ident]) extends Statement {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (defs, "defs") += (embDefs, "embDefs") += (free, "free")
  def copy(defs: Vector[Expr] = defs, embDefs: Vector[EmbeddedExpr] = embDefs, free: Vector[Ident] = free): Let =
    Let(defs, embDefs, free).setPos(pos)
}

final case class Def(name: Ident, args: Vector[IdentOrWildcard], operator: Boolean, payloadType: PayloadType, embeddedId: Option[Ident], ret: Vector[IdentOrWildcard], rules: Vector[DefRule]) extends Statement {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (name, "name") += (args, "args") += (embeddedId, "embeddedId") += (ret, "ret") += (rules, "rules")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"operator=$operator, payloadType=$payloadType")
  def copy(name: Ident = name, args: Vector[IdentOrWildcard] = args, operator: Boolean = operator, payloadType: PayloadType = payloadType, embeddedId: Option[Ident] = embeddedId, ret: Vector[IdentOrWildcard] = ret, rules: Vector[DefRule] = rules): Def =
    Def(name, args, operator, payloadType, embeddedId, ret, rules).setPos(pos)
}
final case class DefRule(on: Vector[Expr], reduced: Vector[Branch]) extends Node {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (on, "on") += (reduced, "reduced")
  def copy(on: Vector[Expr] = on, reduced: Vector[Branch] = reduced): DefRule = DefRule(on, reduced).setPos(pos)
}

final case class Match(on: Vector[Expr], reduced: Vector[Branch]) extends Statement {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (on, "on") += (reduced, "reduced")
  def copy(on: Vector[Expr] = on, reduced: Vector[Branch] = reduced): Match = Match(on, reduced).setPos(pos)
}

final case class Branch(cond: Option[EmbeddedExpr], embRed: Vector[EmbeddedExpr], reduced: Vector[Expr]) extends Node {
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (cond, "cond") += (embRed, "embRed") += (reduced, "reduced")
  def copy(cond: Option[EmbeddedExpr] = cond, embRed: Vector[EmbeddedExpr] = embRed, reduced: Vector[Expr] = reduced): Branch =
    Branch(cond, embRed, reduced).setPos(pos)
}

final class RuleKey(val sym1: Symbol, val sym2: Symbol) {
  override def equals(o: Any): Boolean = o match {
    case o: RuleKey => o.sym1 == sym1 && o.sym2 == sym2 || o.sym1 == sym2 && o.sym2 == sym1
    case _ => false
  }
  override def hashCode(): Int = sym1.hashCode() + sym2.hashCode()
  override def toString: String = s"$sym1 <-> $sym2"
}

sealed trait CheckedRule extends Statement {
  def sym1: Symbol
  def sym2: Symbol
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"${sym1.uniqueStr} . ${sym2.uniqueStr}")
  def key: RuleKey = new RuleKey(sym1, sym2)
}

final case class DerivedRule(sym1: Symbol, sym2: Symbol) extends CheckedRule {
  def copy(sym1: Symbol = sym1, sym2: Symbol = sym2): DerivedRule = DerivedRule(sym1, sym2).setPos(pos)
}

final case class MatchRule(id1: Ident, id2: Ident, args1: Vector[Expr], args2: Vector[Expr],
    emb1: Option[Ident], emb2: Option[Ident], branches: Vector[Branch]) extends CheckedRule {
  def sym1 = id1.sym
  def sym2 = id2.sym
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) =
    n += (args1, "args1") += (args2, "args2") += (emb1, "emb1") += (emb2, "emb2") += (branches, "red")
  def copy(id1: Ident = id1, id2: Ident = id2, args1: Vector[Expr] = args1, args2: Vector[Expr] = args2,
      emb1: Option[Ident] = emb1, emb2: Option[Ident] = emb2, branches: Vector[Branch] = branches): MatchRule =
    MatchRule(id1, id2, args1, args2, emb1, emb2, branches).setPos(pos)
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
  import PayloadType._
  override def toString: String = value match {
    case 0 => "void"
    case 1 => "int"
    case 2 => "ref"
    case 3 => "label"
  }
  def isEmpty: Boolean = !isDefined
  def isDefined: Boolean = this != VOID
  def canCopy: Boolean = this != REF
  def canErase: Boolean = this != REF
  def canCreate: Boolean = this == LABEL
}
object PayloadType {
  final val VOID  = new PayloadType(0)
  final val INT   = new PayloadType(1)
  final val REF   = new PayloadType(2)
  final val LABEL = new PayloadType(3)
  final val PAYLOAD_TYPES_COUNT = 4
}

sealed trait EmbeddedType
object EmbeddedType {
  final case object Unknown extends EmbeddedType
  final case class Payload(payloadType: PayloadType) extends EmbeddedType
  final case class Method(method: java.lang.reflect.Method, ret: EmbeddedType, args:Vector[(EmbeddedType, Boolean /* out */)]) extends EmbeddedType
  final case object Bool extends EmbeddedType
  final val PayloadInt = Payload(PayloadType.INT)
  final val PayloadLabel = Payload(PayloadType.LABEL)
  final val PayloadRef = Payload(PayloadType.REF)
  final val PayloadVoid = Payload(PayloadType.VOID)
}

final class Label(s: String) {
  override def toString: String = s"<$s @ ${System.identityHashCode(this)}>"
}

final class Position(val offset: Int, val file: String, val input: ConvenientParserInput) {
  def pretty: String = {
    if(offset == -1) "unknown"
    else {
      val p = if(input == null) offset.toString else input.prettyIndex(offset)
      s"$file:$p"
    }
  }
  lazy val (line, column) = input.find(offset)
  def isDefined: Boolean = this != Position.unknown
  override def toString: String = s"Position($pretty)"
}
object Position {
  val unknown = new Position(-1, null, null)
  implicit val ordering: Ordering[Position] = Ordering.by(_.offset)
}

trait ShowableNode {
  def showNode: NodeInfo
}

object ShowableNode {
  import MaybeColors._

  def print(n: ShowableNode, out: PrintWriter = new PrintWriter(new OutputStreamWriter(System.out)), name: String = "", prefix: String = "", prefix1: String = null): Unit = {
    def f(n: NodeInfo, pf1: String, pf2: String, name: String, depth: Int): Unit = {
      val b = new StringBuilder()
      val namePrefix = if(name.nonEmpty) s"$name: " else ""
      val msg = n.msg.split('\n')
      val children = n.children.toIndexedSeq
      val cChild = if(depth % 2 == 0) cBlue else cGreen
      b.append(s"$pf1$cCyan$namePrefix$cYellow${n.name}$cNormal ${msg(0)}")
      for(i <- 1 until msg.length) {
        val p = if(children.isEmpty) " " else s"$cChild\u2502"
        val sp = " " * math.max(4, namePrefix.length + n.name.length)
        b.append(s"\n$pf2$p$cNormal$sp${msg(i)}")
      }
      if(n.annot.nonEmpty) b.append(s"  $cBlue${n.annot}$cNormal")
      out.println(b.result())
      children.zipWithIndex.foreach { case ((name, n), idx) =>
        val (p1, p2) = if(idx == children.size-1) ("\u2514 ", "  ") else ("\u251c ", "\u2502 ")
        f(n, pf2 + cChild + p1, pf2 + cChild + p2, name, depth + 1)
      }
    }
    f(NodeInfo(n), if(prefix1 ne null) prefix1 else prefix, prefix, name, 0)
    out.flush()
  }
}

case class NodeInfo(name: String, msg: String = "", children: Iterable[(String, NodeInfo)] = Vector.empty, annot: String = "")

object NodeInfo {
  val empty: NodeInfo = NodeInfo("null")
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
  def += (n: Option[Node]): this.type = { n.foreach(+=); this }
  def += (n: Option[Node], s: String): this.type = { n.foreach(n => buf += ((n, s))); this }
  def += (n: IterableOnce[Node]): this.type = { n.iterator.foreach(+=); this }
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
  def += (n: Option[Node]): this.type = { n.foreach(+=); this }
  def += (n: Option[Node], s: String): this.type = { n.foreach(+=); this }
  def += (n: IterableOnce[Node]): this.type = { n.iterator.foreach(+=); this }
  def += (n: IterableOnce[Node], prefix: String): this.type = { n.iterator.foreach(+=); this }
  def iterator: Iterator[Node] = buf.iterator
}
