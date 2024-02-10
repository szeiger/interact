package de.szeiger.interact

import de.szeiger.interact.BitOps._
import de.szeiger.interact.LongBitOps._
import de.szeiger.interact.ast._

import java.lang.invoke.{MethodHandle, MethodHandles}
import java.lang.reflect.Modifier
import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
 * Deconstruct rules into cells and wires for execution.
 */
class CreateWiring(global: Global) extends Transform with Phase {
  import global._

  override def apply(n: MatchRule) =
    Vector(RuleWiring(n.sym1, n.sym2, n.branches.map(r => BranchWiring(dependencyLoader, n, r)), false).setPos(n.pos))

  override def apply(n: DerivedRule) = {
    if(n.sym1.id == "erase") Vector(deriveErase(n.sym2, n.sym1))
    else if(n.sym1.id == "dup") Vector(deriveDup(n.sym2, n.sym1))
    else super.apply(n)
  }

  override def apply(n: Let) =
    Vector(InitialRuleWiring(n.free.map(_.sym), BranchWiring(dependencyLoader, n)).setPos(n.pos))

  private[this] def deriveErase(sym: Symbol, eraseSym: Symbol): RuleWiring = {
    val cells = Vector.fill(sym.arity)(eraseSym)
    val conns = (0 until sym.arity).map(i => Connection(FreeIdx(1, i), CellIdx(i, -1))).toSet
    val embComp = sym.payloadType match {
      case PayloadType.REF => Vector(PayloadMethodApplication(dependencyLoader, classOf[Runtime.type].getName, "eraseRef", Vector(EmbArg.Active(1)),
        EmbeddedType.PayloadVoid, Vector((EmbeddedType.PayloadRef, false))))
      case _ => Vector.empty
    }
    RuleWiring(eraseSym, sym, Vector(new BranchWiring(0, cells, conns, embComp, None, Vector.empty, 0)), true)
  }

  private[this] def deriveDup(sym: Symbol, dupSym: Symbol): RuleWiring = {
    if(sym == dupSym) {
      val eliminate = new BranchWiring(
        0,
        Vector.empty,
        Set(
          Connection(FreeIdx(0, 0), FreeIdx(1, 0)),
          Connection(FreeIdx(0, 1), FreeIdx(1, 1))
        ),
        Vector.empty,
        Some(PayloadMethodApplication(dependencyLoader, classOf[Runtime.type].getName, "eqLabel", Vector(EmbArg.Active(0), EmbArg.Active(1)),
          EmbeddedType.Bool, Vector((EmbeddedType.PayloadLabel, false), (EmbeddedType.PayloadLabel, false)))),
        Vector.empty, 0
      )
      val commute = new BranchWiring(
        0,
        Vector.fill(4)(dupSym),
        Set(
          Connection(CellIdx(0, 0), CellIdx(2, 0)),
          Connection(CellIdx(0, 1), CellIdx(3, 0)),
          Connection(CellIdx(1, 0), CellIdx(2, 1)),
          Connection(CellIdx(1, 1), CellIdx(3, 1)),
          Connection(CellIdx(0, -1), FreeIdx(0, 0)),
          Connection(CellIdx(1, -1), FreeIdx(0, 1)),
          Connection(CellIdx(2, -1), FreeIdx(1, 0)),
          Connection(CellIdx(3, -1), FreeIdx(1, 1)),
        ),
        Vector(
          PayloadAssignment(EmbArg.Active(1), EmbArg.Cell(0), PayloadType.LABEL),
          PayloadAssignment(EmbArg.Active(1), EmbArg.Cell(1), PayloadType.LABEL),
          PayloadAssignment(EmbArg.Active(0), EmbArg.Cell(2), PayloadType.LABEL),
          PayloadAssignment(EmbArg.Active(0), EmbArg.Cell(3), PayloadType.LABEL),
        ),
        None,
        Vector.empty, 0
      )
      RuleWiring(dupSym, sym, Vector(eliminate, commute), true)
    } else {
      val cells = Vector.fill(sym.arity)(dupSym) ++ Array.fill(2)(sym)
      val conns = Set.newBuilder[Connection]
      for(i <- 0 until sym.arity) {
        conns += Connection(CellIdx(i, 0), CellIdx(sym.arity, i))
        conns += Connection(CellIdx(i, 1), CellIdx(sym.arity+1, i))
      }
      conns += Connection(FreeIdx(0, 0), CellIdx(sym.arity, -1))
      conns += Connection(FreeIdx(0, 1), CellIdx(sym.arity+1, -1))
      conns ++= (0 until sym.arity).map(i => Connection(FreeIdx(1, i), CellIdx(i, -1)))
      val embComp = sym.payloadType match {
        case PayloadType.REF => Vector(PayloadMethodApplication(dependencyLoader, classOf[Runtime.type].getName, "dupRef",
          Vector(EmbArg.Active(1), EmbArg.Cell(sym.arity), EmbArg.Cell(sym.arity+1)),
          EmbeddedType.PayloadVoid,
          Vector((EmbeddedType.PayloadRef, false), (EmbeddedType.PayloadRef, true), (EmbeddedType.PayloadRef, true))))
        case _ => Vector.empty
      }
      val copyLabel = (for(i <- 0 until sym.arity) yield PayloadAssignment(EmbArg.Active(0), EmbArg.Cell(i), PayloadType.LABEL)).toVector
      RuleWiring(dupSym, sym, Vector(new BranchWiring(0, cells, conns.result(), copyLabel ++ embComp, None, Vector.empty, 0)), true)
    }
  }
}

case class Connection(c1: Idx, c2: Idx) extends Node {
  def isExternal: Boolean = c1.isInstanceOf[FreeIdx] || c2.isInstanceOf[FreeIdx]

  def show = s"${c1.show} <-> ${c2.show}"
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)

  override def hashCode: Int = c1.hashCode + c2.hashCode
  override def equals(obj: Any): Boolean = obj match {
    case c: Connection => (c.c1 == c1 && c.c2 == c2) || (c.c1 == c2 && c.c2 == c1)
    case _ => false
  }
}
object Connection {
  implicit val ord: Ordering[Connection] = Ordering.by(_.c1)
}

sealed abstract class Idx {
  def port: Int
  def show: String
  def isAux: Boolean = port >= 0
  def isPrincipal: Boolean = !isAux
}
object Idx {
  implicit val ord: Ordering[Idx] = Ordering.by(_.show)
}
case class CellIdx(idx: Int, port: Int) extends Idx {
  def show = if(idx == -1) s"null:$port" else s"c$idx:$port"
}
case class FreeIdx(active: Int, port: Int) extends Idx {
  def show = s"f$active:$port"
}

sealed abstract class EmbArg extends Node
object EmbArg {
  final case class Active(idx: Int) extends EmbArg
  final case class Cell(idx: Int) extends EmbArg {
    override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$idx")
  }
  final case class Const(v: Any) extends EmbArg {
    override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$v")
  }
  final case class Temp(idx: Int, pt: PayloadType) extends EmbArg
}

sealed abstract class PayloadComputationPlan extends Node

sealed abstract class PayloadComputation extends PayloadComputationPlan {
  def embArgs: Vector[EmbArg]
}

final case class PayloadAssignment(sourceIdx: EmbArg, targetIdx: EmbArg, payloadType: PayloadType) extends PayloadComputation {
  val embArgs: Vector[EmbArg] = Vector(sourceIdx, targetIdx)
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$targetIdx := $sourceIdx, $payloadType")
  override def toString: String = s"PayloadAssignment(${namedNodes.msg})"
}

final case class CreateLabelsComp(name: String, embArgs: Vector[EmbArg]) extends PayloadComputation {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$name, ${embArgs.mkString(", ")}")
  override def toString: String = s"CreateLabelsComp(${namedNodes.msg})"
}

final case class ReuseLabelsComp(cellIdx: Int, embArgs: Vector[EmbArg]) extends PayloadComputationPlan {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$cellIdx, ${embArgs.mkString(", ")}")
  override def toString: String = s"ReuseLabelsComp(${namedNodes.msg})"
}

final case class AllocateTemp(ea: EmbArg.Temp, boxed: Boolean) extends PayloadComputationPlan {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$ea, $boxed")
}

// Check if a FreeIdx is connected to the principal port of a cell with the given Symbol
final case class CheckPrincipal(wire: FreeIdx, sym: Symbol) extends PayloadComputationPlan {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$wire, $sym")
}

final case class PayloadMethodApplication(embTp: EmbeddedType.Method, embArgs: Vector[EmbArg]) extends PayloadComputation {
  def jMethod = embTp.method
  def isStatic: Boolean = Modifier.isStatic(jMethod.getModifiers)
  private[this] lazy val mh = MethodHandles.lookup().unreflect(jMethod)
  lazy val adaptedmh: MethodHandle =
    if(isStatic) mh else MethodHandles.insertArguments(mh, 0, jMethod.getDeclaringClass.getField("MODULE$").get(null))
  override def toString: String = s"PayloadMethodApplication(${namedNodes.msg})"
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"${jMethod.getDeclaringClass.getName}#${jMethod.getName}(${embArgs.mkString(", ")}), ${mh.`type`().descriptorString()}")
}

object PayloadMethodApplication {
  def apply(cl: ClassLoader, cls: String, method: String, embArgs: Vector[EmbArg], ret: EmbeddedType, args: Vector[(EmbeddedType, Boolean)]): PayloadMethodApplication = {
    val c = cl.loadClass(cls)
    val m = c.getMethods.find(_.getName == method).getOrElse(sys.error(s"Method $method not found in $cls"))
    new PayloadMethodApplication(EmbeddedType.Method(m, ret, args), embArgs)
  }
}

final case class PayloadMethodApplicationWithReturn(method: PayloadMethodApplication, retIndex: EmbArg) extends PayloadComputation {
  val embArgs: Vector[EmbArg] = method.embArgs :+ retIndex
  override def toString: String = s"PayloadMethodApplicationWithReturn($method, $retIndex)"
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$retIndex") += method
}

object PayloadComputation {
  def apply(cl: ClassLoader, e: EmbeddedExpr)(handleArg: Symbol => EmbArg): PayloadComputation = e match {
    case EmbeddedAssignment(lhs: Ident, emb: EmbeddedApply) =>
      val ac = apply(cl, emb)(handleArg)
      new PayloadMethodApplicationWithReturn(ac.asInstanceOf[PayloadMethodApplication], handleArg(lhs.sym))
    case EmbeddedAssignment(lhs: Ident, StringLit(v)) =>
      assert(lhs.sym.payloadType == PayloadType.REF)
      new PayloadAssignment(EmbArg.Const(v), handleArg(lhs.sym), PayloadType.REF)
    case EmbeddedAssignment(lhs: Ident, IntLit(v)) =>
      assert(lhs.sym.payloadType == PayloadType.INT)
      new PayloadAssignment(EmbArg.Const(v), handleArg(lhs.sym), PayloadType.INT)
    case EmbeddedAssignment(lhs: Ident, rhs: Ident) =>
      assert(lhs.sym.payloadType == rhs.sym.payloadType)
      new PayloadAssignment(handleArg(rhs.sym), handleArg(lhs.sym), lhs.sym.payloadType)
    case emb @ EmbeddedApply(_, args, _, embTp: EmbeddedType.Method) =>
      val embArgs = args.map {
        case IntLit(v) => EmbArg.Const(v)
        case StringLit(v) => EmbArg.Const(v)
        case id: Ident => handleArg(id.sym)
        //TODO resolve nested applications in CleanEmbedded
      }
      new PayloadMethodApplication(embTp, embArgs)
    case CreateLabels(base, labels) =>
      new CreateLabelsComp(base.id, labels.map(handleArg))
    case _ => CompilerResult.fail(s"Unsupported computation", atNode = e)
  }
}

final case class BranchWiring(cellOffset: Int, cells: Vector[Symbol], conns: Set[Connection], payloadComps: Vector[PayloadComputation],
  cond: Option[PayloadComputation], branches: Vector[BranchWiring], tempOffset: Int) extends Node {
  lazy val (extConns, intConns) = conns.partition(_.isExternal)

  // Aux connections & principal connections by cell & port.
  // Array indices correspond to cell indices, but the Idx values have the cellOffset applied.
  lazy val (auxConns, principalConns) = {
    val a = new Array[Array[Idx]](cells.length)
    for(i <- cells.indices) a(i) = new Array[Idx](cells(i).arity)
    val p = new Array[Idx](cells.length)
    def set(c1: Idx, c2: Idx): Unit = c1 match {
      case CellIdx(i1, p1) => if(p1 >= 0) a(i1-cellOffset)(p1) = c2 else p(i1-cellOffset) = c2
      case _ =>
    }
    conns.foreach { case Connection(c1, c2) => set(c1, c2); set(c2, c1) }
    (a, p)
  }

  def show: String = cells.zipWithIndex.map { case (s, i) => s"${i+cellOffset}: $s/${s.arity}"}.mkString(s"tempO=$tempOffset, cells = [", ", ", "]")

  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) =
    n += (intConns, "i") += (extConns, "e") += (payloadComps, "p") += (cond, "cond") += (branches, "b")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
  def copy(cellOffset: Int = cellOffset, cells: Vector[Symbol] = cells, conns: Set[Connection] = conns,
    payloadComps: Vector[PayloadComputation] = payloadComps, cond: Option[PayloadComputation] = cond,
    branches: Vector[BranchWiring] = branches, tempOffset: Int = tempOffset): BranchWiring =
    BranchWiring(cellOffset, cells, conns, payloadComps, cond, branches, tempOffset).setPos(pos)
}

// Efficiently packed data for direct use in the interpreters
class PackedBranchWiring(bp: BranchWiring, rp: GenericRuleWiring) {
  private[this] def packIdx(idx: Idx): (Int, Int) = idx match {
    case CellIdx(i, p) => (i, p)
    case FreeIdx(0, p) => (-1-p, 0)
    case FreeIdx(1, p) => (-1-p-rp.arity1, 0)
  }
  private[this] def packConn(conn: Connection): Int = {
    val (b0, b1) = packIdx(conn.c1)
    val (b2, b3) = packIdx(conn.c2)
    checkedIntOfBytes(b0, b1, b2, b3)
  }
  private[this] def packConnLong(conn: Connection): Long = {
    val (s0, s1) = packIdx(conn.c1)
    val (s2, s3) = packIdx(conn.c2)
    checkedLongOfShorts(s0, s1, s2, s3)
  }
  lazy val connectionsPacked: Array[Int] = bp.intConns.iterator.map(packConn).toArray
  lazy val connectionsPackedLong: Array[Long] = bp.intConns.iterator.map(packConnLong).toArray
  lazy val freeWiresPacked: Array[Int] = {
    val a = new Array[Int](rp.arity1 + rp.arity2)
    def set(f: FreeIdx, idx2: Idx): Unit = {
      val (s0, s1) = packIdx(idx2)
      a(if(f.active == 1) rp.arity1 + f.port else f.port) = checkedIntOfShorts(s0, s1)
    }
    bp.extConns.foreach { case Connection(i1, i2) =>
      i1 match { case f: FreeIdx => set(f, i2); case _ => }
      i2 match { case f: FreeIdx => set(f, i1); case _ => }
    }
    a
  }
  lazy val (freeWiresPacked1, freWiresPacked2) = freeWiresPacked.splitAt(rp.arity1)
}

object BranchWiring {
  def apply(cl: ClassLoader, let: Let): BranchWiring = CompilerResult.tryInternal(let) {
    val freeLookup = let.free.iterator.zipWithIndex.map { case (n, i) => (n.sym, -i-1) }.toMap
    apply(cl, None, let.embDefs, let.defs, freeLookup, freeLookup.size, Symbol.NoSymbol, Symbol.NoSymbol).setPos(let.pos)
  }

  def apply(cl: ClassLoader, cr: MatchRule, red: Branch): BranchWiring = CompilerResult.tryInternal(cr) {
    val freeLookup = (cr.args1.iterator ++ cr.args2.iterator).zipWithIndex.map { case (n, i) => (n.asInstanceOf[Ident].sym, -i-1) }.toMap
    assert(freeLookup.size == cr.args1.length + cr.args2.length)
    apply(cl, red.cond, red.embRed, red.reduced, freeLookup, cr.sym1.arity,
      cr.emb1.map(_.sym).getOrElse(Symbol.NoSymbol), cr.emb2.map(_.sym).getOrElse(Symbol.NoSymbol)).setPos(red.pos)
  }

  private[this] def apply(cl: ClassLoader, cond: Option[EmbeddedExpr], embRed: Vector[EmbeddedExpr], reduced: Vector[Expr],
      freeLookup: Map[Symbol, Int], arity1: Int, emb1: Symbol, emb2: Symbol): BranchWiring = {
    val cells = ArrayBuffer.empty[Symbol]
    val conns = Set.newBuilder[Connection]
    val cellEmbSyms = mutable.HashMap.empty[Symbol, EmbArg]
    if(emb1.isDefined) cellEmbSyms.put(emb1, EmbArg.Active(0))
    if(emb2.isDefined) cellEmbSyms.put(emb2, EmbArg.Active(1))
    def mkFreeIdx(idx: Int): FreeIdx = FreeIdx(if(idx >= arity1) 1 else 0, if(idx >= arity1) idx-arity1 else idx)
    def mkIdx(t: Int, p: Int): Idx = if(t >= 0) CellIdx(t, p) else mkFreeIdx(-1-t)

    val embComps = ArrayBuffer.empty[PayloadComputation]

    val sc = new Scope[Int] {
      def createCell(sym: Symbol, emb: Option[EmbeddedExpr]): Int = {
        assert(!sym.isEmbedded, s"Unexpected embedded symbol $sym in createCell()")
        if(sym.isCons) {
          val cellIdx = cells.length
          cells += sym
          emb.foreach { case id: Ident => cellEmbSyms.put(id.sym, EmbArg.Cell(cellIdx)) }
          cellIdx
        } else freeLookup(sym)
      }
      def connectCells(c1: Int, p1: Int, c2: Int, p2: Int): Unit =
        conns += Connection(mkIdx(c1, p1), mkIdx(c2, p2))
    }
    sc.addExprs(reduced)
    embComps ++= embRed.map { ee => PayloadComputation(cl, ee)(cellEmbSyms) }
    val condComp = cond.map { ee => PayloadComputation(cl, ee)(cellEmbSyms) }

    new BranchWiring(0, cells.toVector, conns.result(), embComps.toVector, condComp, Vector.empty, 0)
  }

  private[this] abstract class Scope[CellRef] { self =>
    val freeWires = mutable.HashSet.empty[CellRef]

    def createCell(sym: Symbol, payload: Option[EmbeddedExpr]): CellRef
    def connectCells(c1: CellRef, p1: Int, c2: CellRef, p2: Int): Unit

    final def addExprs(defs: Iterable[Expr]): Unit = {
      class TempWire { var c: CellRef = _; var p: Int = 0 }
      @tailrec def connectAny(t1: Any, p1: Int, t2: Any, p2: Int): Unit = (t1, t2) match {
        case (t1: TempWire, t2: CellRef @unchecked) => connectAny(t2, p2, t1, p1)
        case (t1: CellRef @unchecked, t2: TempWire) if t2.c == null => t2.c = t1; t2.p = p1
        case (t1: CellRef @unchecked, t2: TempWire) => connectCells(t1, p1, t2.c, t2.p)
        case (t1: CellRef @unchecked, t2: CellRef @unchecked) => connectCells(t1, p1, t2, p2)
      }
      def foreachSym(e: Expr)(f: Symbol => Unit): Unit = e match {
        case e: Ident => f(e.sym)
        case _: Wildcard =>
        case e: NatLit => f(e.zSym); f(e.sSym)
        case Assignment(l, r) => foreachSym(l)(f); foreachSym(r)(f)
        case Tuple(exprs) => exprs.foreach(e => foreachSym(e)(f))
        case Apply(t, _, args) =>
          foreachSym(t)(f)
          args.foreach(e => foreachSym(e)(f))
        case ApplyCons(t, _, args) =>
          foreachSym(t)(f)
          args.foreach(e => foreachSym(e)(f))
      }
      val refs = new RefsMap
      defs.foreach(e => foreachSym(e) { s =>
        assert(s.isDefined)
        if(!s.isCons) refs.inc(s)
      })
      def cellRet(s: Symbol, c: CellRef): Seq[(Any, Int)] = {
        if(s.isDef) (s.arity-s.returnArity).until(s.arity).map(p => (c, p))
        else Seq((c, -1))
      }
      val bind = mutable.HashMap.empty[Symbol, TempWire]
      def create(e: Expr): Seq[(Any, Int)] = e match {
        case e: NatLit => create(e.expand)
        case i: Ident =>
          val s = i.sym
          assert(s.isDefined)
          refs(s) match {
            case 0 => cellRet(s, createCell(s, None))
            case 1 => val c = createCell(s, None); freeWires.addOne(c); Seq((c, 0))
            case 2 => Seq((bind.getOrElseUpdate(s, new TempWire), -1))
            case _ => CompilerResult.fail(s"Non-linear use of ${i.s} in data", atNode = i)
          }
        case Tuple(es) => es.flatMap(create)
        case Apply(i, emb, args) =>
          val s = i.sym
          assert(s.isCons)
          val c = createCell(s, emb)
          args.zipWithIndex.foreach { case (a, p0) =>
            val p = if(!s.isDef) p0 else p0-1
            val ca = create(a)
            assert(ca.length == 1)
            connectAny(c, p, ca.head._1, ca.head._2)
          }
          cellRet(s, c)
      }
      defs.foreach {
        case Assignment(e1, e2) =>
          val c1 = create(e1)
          val c2 = create(e2)
          assert(c1.length == c2.length)
          c1.zip(c2).foreach { case ((t1, p1), (t2, p2)) => connectAny(t1, p1, t2, p2) }
        case e: Apply =>
          val c = create(e)
          assert(c.isEmpty)
      }
    }
  }
}

abstract class GenericRuleWiring extends Statement {
  def sym1: Symbol
  def sym2: Symbol
  def branches: Vector[BranchWiring]
  def maxCells: Int = branches.iterator.map(_.cells.length).max
  def maxWires: Int = branches.iterator.map(b => b.intConns.size + b.extConns.size).max
  def arity1: Int
  def arity2: Int
  def symFor(rhs: Boolean): Symbol = if(rhs) sym2 else sym1
}

final case class RuleWiring(sym1: Symbol, sym2: Symbol, branches: Vector[BranchWiring], derived: Boolean) extends GenericRuleWiring {
  val key: RuleKey = new RuleKey(sym1, sym2)
  def arity1: Int = sym1.arity
  def arity2: Int = sym2.arity

  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += branches
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$sym1/${sym1.arity} <-> $sym2/${sym2.arity}")
}

// A rule-like object to perform the initial setup; lhs connects to free wires
final case class InitialRuleWiring(free: Vector[Symbol], branch: BranchWiring) extends GenericRuleWiring {
  def sym1 = Symbol.NoSymbol
  def sym2 = Symbol.NoSymbol
  def branches = Vector(branch)
  def arity1: Int = free.length
  def arity2: Int = 0

  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += branch
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(free.mkString(", "))
}
