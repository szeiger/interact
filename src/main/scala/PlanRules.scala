package de.szeiger.interact

import de.szeiger.interact.BitOps._
import de.szeiger.interact.LongBitOps._
import de.szeiger.interact.ast._

import java.lang.invoke.{MethodHandle, MethodHandles}
import java.lang.reflect.Modifier
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.jdk.CollectionConverters._

/**
 * Deconstruct rules into cells and wires for execution.
 */
class PlanRules(global: Global) extends Transform with Phase {
  import global._

  override def apply(n: MatchRule) =
    Vector(RulePlan(n.sym1, n.sym2, n.reduction.map(r => BranchPlan(dependencyLoader, n, r))).setPos(n.pos))

  override def apply(n: DerivedRule) = {
    if(n.sym1.id == "erase") Vector(deriveErase(n.sym2, n.sym1))
    else if(n.sym1.id == "dup") Vector(deriveDup(n.sym2, n.sym1))
    else super.apply(n)
  }

  override def apply(n: Let) =
    Vector(InitialPlan(n.free.map(_.sym), BranchPlan(dependencyLoader, n)).setPos(n.pos))

  private[this] def deriveErase(sym: Symbol, eraseSym: Symbol): RulePlan = {
    val cells = Vector.fill(sym.arity)(eraseSym)
    val wireConns: Vector[Connection] = (0 until sym.arity).map(i => Connection(FreeIdx(true, i), CellIdx(i, -1))).toVector
    val embComp = sym.payloadType match {
      case PayloadType.REF => Seq(new EmbeddedMethodApplication(dependencyLoader, classOf[Intrinsics.type].getName, "eraseRef", Nil, Array(-2), null))
      case _ => Nil
    }
    RulePlan(eraseSym, sym, Vector(new BranchPlan(0, cells, Vector.empty, wireConns, Array(), embComp, None)))
  }

  private[this] def deriveDup(sym: Symbol, dupSym: Symbol): RulePlan = {
    if(sym == dupSym) {
      val wireConns = Vector(Connection(FreeIdx(false, 0), FreeIdx(true, 0)), Connection(FreeIdx(false, 1), FreeIdx(true, 1)))
      RulePlan(dupSym, sym, Vector(new BranchPlan(2, Vector.empty, Vector.empty, wireConns, Array(), Nil, None)))
    } else {
      val cells = Vector.fill(sym.arity)(dupSym) ++ Array.fill(2)(sym)
      val internalConns = Vector.newBuilder[Connection]
      for(i <- 0 until sym.arity) {
        internalConns += Connection(CellIdx(i, 0), CellIdx(sym.arity, i))
        internalConns += Connection(CellIdx(i, 1), CellIdx(sym.arity+1, i))
      }
      val wireConns1 = Vector(Connection(FreeIdx(false, 0), CellIdx(sym.arity, -1)), Connection(FreeIdx(false, 1), CellIdx(sym.arity+1, -1)))
      val wireConns2 = (0 until sym.arity).map(i => Connection(FreeIdx(true, i), CellIdx(i, -1)))
      val embComp = sym.payloadType match {
        case PayloadType.REF => Seq(new EmbeddedMethodApplication(dependencyLoader, classOf[Intrinsics.type].getName, "dupRef", Nil, Array(-2, sym.arity, sym.arity+1), null))
        case _ => Nil
      }
      RulePlan(dupSym, sym, Vector(new BranchPlan(2, cells, internalConns.result(), wireConns1 ++ wireConns2, Array(), embComp, None)))
    }
  }
}

case class Connection(c1: Idx, c2: Idx) extends Node {
  def show = s"${c1.show} <-> ${c2.show}"
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
  def mapCell(m: Map[Int, Int]): Connection = {
    val c1m = c1.mapCell(m)
    val c2m = c2.mapCell(m)
    if((c1m eq c1) && (c2m eq c2)) this else Connection(c1m, c2m)
  }
}
object Connection {
  implicit val ord: Ordering[Connection] = Ordering.by(_.c1)
}

sealed abstract class Idx {
  def show: String
  def mapCell(m: Map[Int, Int]): Idx
}
object Idx {
  implicit val ord: Ordering[Idx] = Ordering.by(_.show)
}
case class CellIdx(idx: Int, port: Int) extends Idx {
  def show = s"c$idx:$port"
  def mapCell(m: Map[Int, Int]): Idx = {
    val i2 = m(idx)
    if(i2 == idx) this else CellIdx(i2, port)
  }
}
case class FreeIdx(rhs: Boolean, port: Int) extends Idx {
  def show = if(rhs) s"rhs:$port" else s"lhs:$port"
  def mapCell(m: Map[Int, Int]): Idx = this
}

trait IntBox { def getValue: Int; def setValue(i: Int): Unit }
trait RefBox { def getValue: AnyRef; def setValue(o: AnyRef): Unit } // Also used for Label
trait LifecycleManaged { def erase(): Unit; def copy(): LifecycleManaged }

sealed abstract class PayloadAssigner(val cellIdx: Int) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit
  def mapCell(m: Map[Int, Int]): PayloadAssigner
}
class IntLHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[IntBox].setValue(lhs.asInstanceOf[IntBox].getValue)
  def mapCell(m: Map[Int, Int]): PayloadAssigner = {
    val c = m(cellIdx)
    if(c == cellIdx) this else new IntLHSMover(c)
  }
}
class IntRHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[IntBox].setValue(rhs.asInstanceOf[IntBox].getValue)
  def mapCell(m: Map[Int, Int]): PayloadAssigner = {
    val c = m(cellIdx)
    if(c == cellIdx) this else new IntRHSMover(c)
  }
}
class RefLHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[RefBox].setValue(lhs.asInstanceOf[RefBox].getValue)
  def mapCell(m: Map[Int, Int]): PayloadAssigner = {
    val c = m(cellIdx)
    if(c == cellIdx) this else new RefLHSMover(c)
  }
}
class RefRHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[RefBox].setValue(rhs.asInstanceOf[RefBox].getValue)
  def mapCell(m: Map[Int, Int]): PayloadAssigner = {
    val c = m(cellIdx)
    if(c == cellIdx) this else new RefRHSMover(c)
  }
}
class EmbeddedComputationAssigner(_cellIdx: Int, ec: EmbeddedComputation[Int]) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = {
    val args = ec.argIndices.map {
      case -1 => lhs match {
        case c: RefBox => c.getValue
        case c: IntBox => c.getValue
      }
      case -2 => rhs match {
        case c: RefBox => c.getValue
        case c: IntBox => c.getValue
      }
    }
    val v = ec.invoke(args)
    target match {
      case c: RefBox => c.setValue(v.asInstanceOf[AnyRef])
      case c: IntBox => c.setValue(v.asInstanceOf[Int])
    }
  }
  def mapCell(m: Map[Int, Int]): PayloadAssigner = {
    val c = m(cellIdx)
    if(c == cellIdx) this else new EmbeddedComputationAssigner(c, ec)
  }
}

abstract class EmbeddedComputation[A](val argIndices: scala.collection.Seq[A]) {
  def invoke(args: scala.collection.Seq[Any]): Any
  def argArity: Int = argIndices.length
}

final class EmbeddedCreateLabels[A](name: String, _argIndices: scala.collection.Seq[A]) extends EmbeddedComputation[A](_argIndices) {
  def invoke(args: scala.collection.Seq[Any]): Any = {
    val label = new Label(name)
    args.foreach(_.asInstanceOf[RefBox].setValue(label))
    label
  }
}

final class EmbeddedMethodApplication[A](cl: ClassLoader, cls: String, method: String, consts: Iterable[(Int, Any)],
  _argIndices: scala.collection.IndexedSeq[A], subComps: Array[EmbeddedComputation[A]]) extends EmbeddedComputation(_argIndices) {
  private val mh: MethodHandle = {
    val c = cl.loadClass(cls)
    val m = c.getMethods.find(_.getName == method).getOrElse(sys.error(s"Method $method not found in $cls"))
    var mh = MethodHandles.lookup().unreflect(m)
    if(!Modifier.isStatic(m.getModifiers)) mh = MethodHandles.insertArguments(mh, 0, c.getField("MODULE$").get(null))
    for((pos, v) <- consts) mh = MethodHandles.insertArguments(mh, pos, v)
    mh
  }
  def invoke(args: scala.collection.Seq[Any]): Any = {
    if(subComps == null) mh.invokeWithArguments(args.asJava)
    else {
      var i, j = 0
      val mhArgs = new Array[Any](subComps.length)
      while(i < mhArgs.length) {
        if(subComps(i) == null) {
          mhArgs(i) = args(j)
          j += 1
        } else {
          val sub = subComps(i)
          val sa = sub.argArity
          val subArgs = args.slice(j, j+sa)
          j += sa
          mhArgs(i) = sub.invoke(subArgs)
        }
        i += 1
      }
      mh.invokeWithArguments(mhArgs: _*)
    }
  }
}

final class EmbeddedMethodApplicationWithReturn[A](method: EmbeddedComputation[A], retIndex: A) extends EmbeddedComputation[A](method.argIndices :+ retIndex) {
  def invoke(args: scala.collection.Seq[Any]): Unit = {
    val ret = method.invoke(args.init)
    args.last match {
      case b: IntBox => b.setValue(ret.asInstanceOf[Int])
      case b: RefBox => b.setValue(ret.asInstanceOf[AnyRef])
    }
  }
}

final class EmbeddedConstantIntAssigner[A](retIndex: A, value: Int) extends EmbeddedComputation(Vector(retIndex)) {
  def invoke(args: scala.collection.Seq[Any]): Unit =
    args.head.asInstanceOf[IntBox].setValue(value)
}

final class EmbeddedConstantRefAssigner[A](retIndex: A, value: AnyRef) extends EmbeddedComputation(Vector(retIndex)) {
  def invoke(args: scala.collection.Seq[Any]): Unit =
    args.head.asInstanceOf[RefBox].setValue(value)
}

object EmbeddedComputation {
  private[this] val operators = Map(
    "==" -> (Intrinsics.getClass.getName, "eq"),
    "+" -> (Intrinsics.getClass.getName, "intAdd"),
    "-" -> (Intrinsics.getClass.getName, "intSub"),
  )

  def apply[A](cl: ClassLoader, e: EmbeddedExpr)(handleArg: Symbol => A): EmbeddedComputation[A] = e match {
    case EmbeddedAssignment(lhs: Ident, emb: EmbeddedApply) =>
      val ac = apply(cl, emb)(handleArg)
      new EmbeddedMethodApplicationWithReturn[A](ac, handleArg(lhs.sym))
    case EmbeddedAssignment(lhs: Ident, StringLit(v)) =>
      new EmbeddedConstantRefAssigner[A](handleArg(lhs.sym), v)
    case EmbeddedAssignment(lhs: Ident, IntLit(v)) =>
      new EmbeddedConstantIntAssigner[A](handleArg(lhs.sym), v)
    case emb @ EmbeddedApply(_, args, op, _) =>
      val consts = mutable.ArrayBuffer.empty[(Int, Any)]
      val argIndices = mutable.ArrayBuffer.empty[A]
      var offset = 0
      var subComps: Array[EmbeddedComputation[A]] = null
      args.zipWithIndex.foreach {
        case (IntLit(v), i) =>
          consts += ((i-offset, v))
          offset += 1
        case (StringLit(v), i) =>
          consts += ((i-offset, v))
          offset += 1
        case (id: Ident, _) =>
          argIndices += handleArg(id.sym)
        case (a: EmbeddedApply, i) =>
          if(subComps == null) subComps = new Array(args.length)
          val sub = apply(cl, a)(handleArg)
          subComps(i) = sub
          argIndices ++= sub.argIndices
      }
      val (cln, mn) =
        if(op) operators(emb.methodQN.head) else (emb.className, emb.methodName)
      new EmbeddedMethodApplication(cl, cln, mn, consts, argIndices, subComps)
    case CreateLabels(base, labels) =>
      new EmbeddedCreateLabels[A](base.id, labels.map(handleArg))
    case _ => CompilerResult.fail(s"Embedded computation must be a method call", atNode = e)
  }
}

final class BranchPlan(arity1: Int,
  val cells: Vector[Symbol],
  val internalConnsDistinct: Vector[Connection],
  val wireConnsByWire: Vector[Connection],
  val assigners: Array[PayloadAssigner],
  val embeddedComps: Seq[EmbeddedComputation[Int]],
  val condition: Option[EmbeddedComputation[Int]]) extends Node {

  lazy val wireConnsDistinct: Vector[Connection] = wireConnsByWire.filter {
    case Connection(FreeIdx(r1, i1), FreeIdx(r2, i2)) =>
      if(r1 == r2) i1 < i2 else r1 < r2
    case _ => true
  }

  // Efficiently packed data for direct use in the interpreters:
  private[this] def packIdx(idx: Idx): (Int, Int) = idx match {
    case CellIdx(i, p) => (i, p)
    case FreeIdx(false, p) => (-1-p, 0)
    case FreeIdx(true, p) => (-1-p-arity1, 0)
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
  lazy val connectionsPacked: Array[Int] = internalConnsDistinct.iterator.map(packConn).toArray
  lazy val connectionsPackedLong: Array[Long] = internalConnsDistinct.iterator.map(packConnLong).toArray
  lazy val freeWiresPacked: Array[Int] = {
    val a = new Array[Int](wireConnsByWire.length)
    wireConnsByWire.foreach { case c @ Connection(f @ FreeIdx(rhs, i), idx2) =>
      val (s0, s1) = packIdx(idx2)
      a(if(rhs) arity1 + i else i) = checkedIntOfShorts(s0, s1)
    }
    a
  }
  lazy val (freeWiresPacked1, freWiresPacked2) = freeWiresPacked.splitAt(arity1)

  // Aux connections by cell & port
  lazy val cellConns: Array[Array[Idx]] = {
    val a = new Array[Array[Idx]](cells.length)
    for(i <- cells.indices) a(i) = new Array[Idx](cells(i).arity)
    def f(cs: Iterable[Connection]): Unit = cs.foreach {
      case Connection(c1: CellIdx, c2: CellIdx) =>
        if(c1.port >= 0) a(c1.idx)(c1.port) = c2
        if(c2.port >= 0) a(c2.idx)(c2.port) = c1
      case Connection(c1: CellIdx, c2) if c1.port >= 0 => a(c1.idx)(c1.port) = c2
      case Connection(c1, c2: CellIdx) if c2.port >= 0 => a(c2.idx)(c2.port) = c1
      case _ =>
    }
    f(internalConnsDistinct)
    f(wireConnsByWire)
    a
  }

  def show: String = cells.zipWithIndex.map { case (s, i) => s"$i: $s/${s.arity}"}.mkString("cells = [", ", ", "]")

  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += (internalConnsDistinct, "i") += (wireConnsByWire, "w")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
}

object BranchPlan {
  def apply(cl: ClassLoader, let: Let): BranchPlan = CompilerResult.tryInternal(let) {
    val freeLookup = let.free.iterator.zipWithIndex.map { case (n, i) => (n.sym, -i-1) }.toMap
    apply(cl, None, let.embDefs, let.defs, freeLookup, freeLookup.size, 0, None, None, PayloadType.VOID, PayloadType.VOID)
  }

  def apply(cl: ClassLoader, cr: MatchRule, red: Branch): BranchPlan = CompilerResult.tryInternal(cr) {
    val freeLookup = (cr.args1.iterator ++ cr.args2.iterator).zipWithIndex.map { case (n, i) => (n.asInstanceOf[Ident].sym, -i-1) }.toMap
    assert(freeLookup.size == cr.args1.length + cr.args2.length)
    apply(cl, red.cond, red.embRed, red.reduced, freeLookup, cr.sym1.arity, cr.sym2.arity, cr.emb1, cr.emb2, cr.sym1.payloadType, cr.sym2.payloadType)
  }

  private[this] def apply(cl: ClassLoader, cond: Option[EmbeddedExpr], embRed: Vector[EmbeddedExpr], reduced: Vector[Expr], freeLookup: Map[Symbol, Int], arity1: Int, arity2: Int,
      emb1: Option[EmbeddedExpr], emb2: Option[EmbeddedExpr], lhsPayloadType: PayloadType, rhsPayloadType: PayloadType): BranchPlan = {
    val cells = mutable.ArrayBuffer.empty[Symbol]
    val internalConns = mutable.HashSet.empty[Connection]
    val wireConns = new Array[Connection](freeLookup.size)
    val assigners = mutable.ArrayBuffer.empty[PayloadAssigner]
    val lhsEmbId = emb1.map(_.asInstanceOf[Ident].s).orNull
    val rhsEmbId = emb2.map(_.asInstanceOf[Ident].s).orNull
    val cellEmbIds = mutable.HashMap.empty[String, ArrayBuffer[Int]]
    if(lhsEmbId != null) cellEmbIds.put(lhsEmbId, ArrayBuffer(-1))
    if(rhsEmbId != null) cellEmbIds.put(rhsEmbId, ArrayBuffer(-2))
    def mkFreeIdx(idx: Int): FreeIdx = FreeIdx(idx >= arity1, if(idx >= arity1) idx-arity1 else idx)
    def mkIdx(t: Int, p: Int): Idx = if(t >= 0) CellIdx(t, p) else mkFreeIdx(-1-t)
    val sc = new Scope[Int] {
      override def createCell(sym: Symbol, emb: Option[EmbeddedExpr]): Int = {
        assert(!sym.isEmbedded, s"Unexpected embedded symbol $sym in createCell()")
        if(sym.isCons) {
          val cellIdx = cells.length
          cells += sym
          emb.foreach { case Ident(id) =>
            if(id == lhsEmbId) assigners += (if(sym.payloadType == PayloadType.INT) new IntLHSMover(cellIdx) else new RefLHSMover(cellIdx))
            else if(id == rhsEmbId) assigners += (if(sym.payloadType == PayloadType.INT) new IntRHSMover(cellIdx) else new RefRHSMover(cellIdx))
            else cellEmbIds.put(id, ArrayBuffer(cellIdx))
          }
          cellIdx
        } else freeLookup(sym)
      }
      override def connectCells(c1: Int, p1: Int, c2: Int, p2: Int): Unit = {
        if(c1 >= 0 && c2 >= 0) {
          val ci1 = CellIdx(c1, p1)
          val ci2 = CellIdx(c2, p2)
          if(!internalConns.contains(Connection(ci2, ci1)))
            internalConns.add(Connection(ci1, ci2))
        } else {
          if(c1 < 0) wireConns(-1-c1) = Connection(mkIdx(c1, p1), mkIdx(c2, p2))
          if(c2 < 0) wireConns(-1-c2) = Connection(mkIdx(c2, p2), mkIdx(c1, p1))
        }
      }
    }
    sc.addExprs(reduced)
    def payloadTypeForIdent(s: String): PayloadType = cellEmbIds(s).head match {
      case -1 => lhsPayloadType
      case -2 => rhsPayloadType
      case i => cells(i).payloadType
    }
    val embComp = embRed.map { ee =>
      val as = mutable.ArrayBuffer.empty[String]
      val ec = EmbeddedComputation(cl, ee) { a => as += a.id; cellEmbIds(a.id).head }
      val refAs = as.filter(s => payloadTypeForIdent(s) == PayloadType.REF)
      assert(refAs.distinct.length == refAs.length)
      ec
    }
    val condComp = cond.map { ee => EmbeddedComputation(cl, ee)(s => cellEmbIds(s.id).head) }
    cells.foreach(c => assert(c != null))
    internalConns.foreach(c => assert(c != null))
    wireConns.foreach(c => assert(c != null))
    assigners.foreach(c => assert(c != null))
    embComp.foreach(c => assert(c != null))
    condComp.foreach(c => assert(c != null))

    new BranchPlan(arity1, cells.toVector, internalConns.toVector.sorted, wireConns.toVector, assigners.toArray, embComp, condComp)
  }
}

abstract class GenericRulePlan extends Statement {
  def sym1: Symbol
  def sym2: Symbol
  def branches: Vector[BranchPlan]
  def maxCells: Int = branches.iterator.map(_.cells.length).max
  def maxWires: Int = branches.iterator.map(b => b.internalConnsDistinct.length + b.wireConnsByWire.length).max
  def arity1: Int
  def arity2: Int
  def symFor(rhs: Boolean): Symbol = if(rhs) sym2 else sym1
}

final case class RulePlan(sym1: Symbol, sym2: Symbol, branches: Vector[BranchPlan]) extends GenericRulePlan {
  def arity1: Int = sym1.arity
  def arity2: Int = sym2.arity

  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += branches
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$sym1/${sym1.arity} <-> $sym2/${sym2.arity}")
}

// A rule-like object to perform the initial setup; lhs connects to free wires
final case class InitialPlan(free: Vector[Symbol], branch: BranchPlan) extends GenericRulePlan {
  def sym1 = Symbol.NoSymbol
  def sym2 = Symbol.NoSymbol
  def branches = Vector(branch)
  def arity1: Int = free.length
  def arity2: Int = 0

  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += branch
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(free.mkString(", "))
}
