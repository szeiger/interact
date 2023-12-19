package de.szeiger.interact

import de.szeiger.interact.mt.BitOps._
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

  private[this] def deriveErase(sym: Symbol, eraseSym: Symbol): RulePlan = {
    val cells = Array.fill(sym.arity)(eraseSym)
    val fwp = (0 until sym.arity).map(i => checkedIntOfShorts(i, -1)).toArray
    val embComp = sym.payloadType match {
      case PayloadType.REF => Seq(new EmbeddedMethodApplication(dependencyLoader, classOf[Intrinsics.type].getName, "eraseRef", Nil, Array(-2), null))
      case _ => Nil
    }
    new RulePlan(eraseSym, sym, Vector(new BranchPlan(0, cells, Array.empty, fwp, Array(), embComp, None)))
  }

  private[this] def deriveDup(sym: Symbol, dupSym: Symbol): RulePlan = {
    if(sym == dupSym)
      new RulePlan(dupSym, sym, Vector(new BranchPlan(2, Array.empty, Array.empty, Array(checkedIntOfShorts(-3, -1), checkedIntOfShorts(-4, -1)), Array(), Nil, None)))
    else {
      val cells = Array.fill(sym.arity)(dupSym) ++ Array.fill(2)(sym)
      val conns = new Array[Int](sym.arity*2)
      for(i <- 0 until sym.arity) {
        conns(i*2) = checkedIntOfBytes(i, 0, sym.arity, i)
        conns(i*2+1) = checkedIntOfBytes(i, 1, sym.arity+1, i)
      }
      val fwp1 = Array[Int](checkedIntOfShorts(sym.arity, -1), checkedIntOfShorts(sym.arity+1, -1))
      val fwp2 = (0 until sym.arity).map(i => checkedIntOfShorts(i, -1)).toArray
      val embComp = sym.payloadType match {
        case PayloadType.REF => Seq(new EmbeddedMethodApplication(dependencyLoader, classOf[Intrinsics.type].getName, "dupRef", Nil, Array(-2, sym.arity, sym.arity+1), null))
        case _ => Nil
      }
      new RulePlan(dupSym, sym, Vector(new BranchPlan(2, cells, conns, fwp1 ++ fwp2, Array(), embComp, None)))
    }
  }
}

case class Connection(c1: Idx, c2: Idx) { def str = s"${c1.str} <-> ${c2.str}" }

sealed abstract class Idx { def str: String }
case class CellIdx(idx: Int, port: Int) extends Idx { def str = s"c$idx:$port" }
case class FreeIdx(rhs: Boolean, idx: Int) extends Idx { def str = if(rhs) s"rhs:$idx" else s"lhs:$idx" }

trait IntBox { def getValue: Int; def setValue(i: Int): Unit }
trait RefBox { def getValue: AnyRef; def setValue(o: AnyRef): Unit } // Also used for Label
trait LifecycleManaged { def erase(): Unit; def copy(): LifecycleManaged }

sealed abstract class PayloadAssigner(val cellIdx: Int) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit
}
class IntLHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[IntBox].setValue(lhs.asInstanceOf[IntBox].getValue)
}
class IntRHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[IntBox].setValue(rhs.asInstanceOf[IntBox].getValue)
}
class RefLHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[RefBox].setValue(lhs.asInstanceOf[RefBox].getValue)
}
class RefRHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[RefBox].setValue(rhs.asInstanceOf[RefBox].getValue)
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

  def apply[A](cl: ClassLoader, e: EmbeddedExpr)(creator: => String)(handleArg: Symbol => A): EmbeddedComputation[A] = e match {
    case EmbeddedAssignment(lhs: Ident, emb: EmbeddedApply) =>
      val ac = apply(cl, emb)(creator)(handleArg)
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
          val sub = apply(cl, a)(creator)(handleArg)
          subComps(i) = sub
          argIndices ++= sub.argIndices
      }
      val (cln, mn) =
        if(op) operators(emb.methodQN.head) else (emb.className, emb.methodName)
      new EmbeddedMethodApplication(cl, cln, mn, consts, argIndices, subComps)
    case CreateLabels(base, labels) =>
      new EmbeddedCreateLabels[A](base.id, labels.map(handleArg))
    case _ => CompilerResult.fail(s"Embedded computation must be a method call in $creator", atNode = e)
  }
}

final class BranchPlan(arity1: Int,
  val cells: Array[Symbol], val connectionsPacked: Array[Int],
  val freeWiresPacked: Array[Int],
  val assigners: Array[PayloadAssigner],
  val embeddedComps: Seq[EmbeddedComputation[Int]],
  val condition: Option[EmbeddedComputation[Int]]) extends Node {

  lazy val (freeWiresPacked1, freWiresPacked2) = freeWiresPacked.splitAt(arity1)

  private[this] def mkFreeIdx(idx: Int): FreeIdx = {
    val rhs = idx >= arity1
    FreeIdx(rhs, if(rhs) idx-arity1 else idx)
  }
  private[this] def mkIdx(t: Int, p: Int): Idx =
    if(t >= 0) CellIdx(t, p) else mkFreeIdx(-1-t)

  lazy val internalConns: Array[Connection] = connectionsPacked.map { i =>
    Connection(mkIdx(byte0(i), byte1(i)), mkIdx(byte2(i), byte3(i)))
  }

  private[this] lazy val wireConns: Array[Connection] = freeWiresPacked.zipWithIndex.map { case (fw, idx) =>
    Connection(mkFreeIdx(idx), mkIdx(short0(fw), short1(fw)))
  }

  lazy val wireConnsDistinct: Array[Connection] = wireConns.filter {
    case Connection(FreeIdx(r1, i1), FreeIdx(r2, i2)) =>
      if(r1 == r2) i1 < i2 else r1 < r2
    case _ => true
  }

  // Connections by cell & port (-1-based, includes principal)
  lazy val cellConns: Array[Array[Idx]] = {
    val a = new Array[Array[Idx]](cells.length)
    for(i <- cells.indices) a(i) = new Array[Idx](cells(i).arity+1)
    def f(cs: Array[Connection]): Unit = cs.foreach {
      case Connection(c1: CellIdx, c2: CellIdx) => a(c1.idx)(c1.port+1) = c2; a(c2.idx)(c2.port+1) = c1
      case Connection(c1: CellIdx, c2) => a(c1.idx)(c1.port+1) = c2
      case Connection(c1, c2: CellIdx) => a(c2.idx)(c2.port+1) = c1
      case _ =>
    }
    f(internalConns)
    f(wireConns)
    a
  }

  def log(): Unit = {
    println(s"  Branch:")
    println("    Cells:")
    cells.zipWithIndex.foreach { case (sym, idx) => println(s"      [$idx] $sym ${sym.arity}") }
    println("    Connections:")
    (internalConns ++ wireConnsDistinct).foreach { c => println(s"      ${c.str}") }
  }
}

object BranchPlan {
  def apply[C](cl: ClassLoader, cr: MatchRule, red: Branch): BranchPlan = CompilerResult.tryInternal(cr) {
    val cells = mutable.ArrayBuffer.empty[Symbol]
    val conns = mutable.HashSet.empty[Int]
    val freeLookup = (cr.args1.iterator ++ cr.args2.iterator).zipWithIndex.map { case (n, i) => (n.asInstanceOf[Ident].sym, -i-1) }.toMap
    assert(freeLookup.size == cr.args1.length + cr.args2.length)
    val fwp = new Array[Int](freeLookup.size)
    val assigners = mutable.ArrayBuffer.empty[PayloadAssigner]
    val lhsEmbId = cr.emb1.map(_.asInstanceOf[Ident].s).orNull
    val rhsEmbId = cr.emb2.map(_.asInstanceOf[Ident].s).orNull
    val cellEmbIds = mutable.HashMap.empty[String, ArrayBuffer[Int]]
    val lhsPayloadType = cr.sym1.payloadType
    val rhsPayloadType = cr.sym2.payloadType
    if(lhsEmbId != null) cellEmbIds.put(lhsEmbId, ArrayBuffer(-1))
    if(rhsEmbId != null) cellEmbIds.put(rhsEmbId, ArrayBuffer(-2))
    def payloadTypeForIdent(s: String): PayloadType = cellEmbIds(s).head match {
      case -1 => lhsPayloadType
      case -2 => rhsPayloadType
      case i => cells(i).payloadType
    }
    val sc = new Scope[Int] {
      override def createCell(sym: Symbol, emb: Option[EmbeddedExpr]): Int = {
        if(sym.isCons) {
          val cellIdx = cells.length
          cells += sym
          emb.foreach {
            case e @ Ident(id) =>
              if(id == lhsEmbId) assigners += (if(sym.payloadType == PayloadType.INT) new IntLHSMover(cellIdx) else new RefLHSMover(cellIdx))
              else if(id == rhsEmbId) assigners += (if(sym.payloadType == PayloadType.INT) new IntRHSMover(cellIdx) else new RefRHSMover(cellIdx))
              else cellEmbIds.put(id, ArrayBuffer(cellIdx))
            case e =>
              CompilerResult.fail(s"Invalid payload expression ${e.show}", atNode = cr)
          }
          cellIdx
        } else freeLookup(sym)
      }
      override def connectCells(c1: Int, p1: Int, c2: Int, p2: Int): Unit = {
        if(c1 >= 0 && c2 >= 0) {
          if(!conns.contains(checkedIntOfBytes(c2, p2, c1, p1)))
            conns.add(checkedIntOfBytes(c1, p1, c2, p2))
        } else {
          if(c1 < 0) fwp(-1-c1) = checkedIntOfShorts(c2, p2)
          if(c2 < 0) fwp(-1-c2) = checkedIntOfShorts(c1, p1)
        }
      }
    }
    sc.addExprs(red.reduced)
    val embComp = red.embRed.map { ee =>
      val as = mutable.ArrayBuffer.empty[String]
      val ec = EmbeddedComputation(cl, ee)(cr.show) { a => as += a.id; cellEmbIds(a.id).head }
      val refAs = as.filter(s => payloadTypeForIdent(s) == PayloadType.REF)
      assert(refAs.distinct.length == refAs.length)
      ec
    }
    val cond = red.cond.map { ee => EmbeddedComputation(cl, ee)(cr.show)(s => cellEmbIds(s.id).head) }
    new BranchPlan(cr.sym1.arity, cells.toArray, conns.toArray, fwp, assigners.toArray, embComp, cond)
  }
}

final case class RulePlan(sym1: Symbol, sym2: Symbol, branches: Vector[BranchPlan]) extends Statement {
  def symFor(rhs: Boolean): Symbol = if(rhs) sym2 else sym1
  def arity1: Int = sym1.arity
  def arity2: Int = sym2.arity
  def maxCells: Int = branches.iterator.map(_.cells.length).max
  def maxWires: Int = branches.iterator.map(b => b.connectionsPacked.length + b.freeWiresPacked.length).max

  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += branches
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$sym1 <-> $sym2")
}
