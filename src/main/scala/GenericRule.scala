package de.szeiger.interact

import de.szeiger.interact.mt.BitOps._
import de.szeiger.interact.ast._

import java.lang.invoke.{MethodHandle, MethodHandles}
import java.lang.reflect.Modifier
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.jdk.CollectionConverters._

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
class IntConstAssigner(_cellIdx: Int, val c: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[IntBox].setValue(c)
}
class IntLHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[IntBox].setValue(lhs.asInstanceOf[IntBox].getValue)
}
class IntRHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[IntBox].setValue(rhs.asInstanceOf[IntBox].getValue)
}
class RefConstAssigner(_cellIdx: Int, val c: AnyRef) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[RefBox].setValue(c)
}
class RefLHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[RefBox].setValue(lhs.asInstanceOf[RefBox].getValue)
}
class RefRHSMover(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[RefBox].setValue(rhs.asInstanceOf[RefBox].getValue)
}
class LabelLHSAssigner(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
  def apply(lhs: AnyRef, rhs: AnyRef, target: AnyRef): Unit = target.asInstanceOf[RefBox].setValue(lhs.asInstanceOf[RefBox].getValue)
}
class LabelRHSAssigner(_cellIdx: Int) extends PayloadAssigner(_cellIdx) {
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

object EmbeddedComputation {
  private[this] val operators = Map(
    "==" -> (Intrinsics.getClass.getName, "eq"),
    "+" -> (Intrinsics.getClass.getName, "intAdd"),
    "-" -> (Intrinsics.getClass.getName, "intSub"),
  )

  def apply[A](cl: ClassLoader, e: EmbeddedExpr)(creator: => String)(handleArg: Symbol => A): EmbeddedComputation[A] = e match {
    case emb @ EmbeddedApply(_, args, op) =>
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
    case _ => sys.error(s"Embedded computation must be a method call in $creator")
  }
}

final class GenericRuleBranch(arity1: Int,
  val cells: Array[Symbol], val connectionsPacked: Array[Int],
  val freeWiresPacked: Array[Int],
  val assigners: Array[PayloadAssigner],
  val embeddedComps: Seq[EmbeddedComputation[Int]],
  val condition: Option[EmbeddedComputation[Int]]) {

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

  lazy val wireConns: Array[Connection] = freeWiresPacked.zipWithIndex.map { case (fw, idx) =>
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

object GenericRuleBranch {
  def apply[C](cl: ClassLoader, cr: MatchRule, red: Branch): GenericRuleBranch = CompilerResult.tryInternal(cr) {
    //println(s"***** Preparing ${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}")
    val cells = mutable.ArrayBuffer.empty[Symbol]
    val conns = mutable.HashSet.empty[Int]
    val freeLookup = (cr.args1.iterator ++ cr.args2.iterator).zipWithIndex.map { case (n, i) => (n.asInstanceOf[Ident].sym, -i-1) }.toMap
    assert(freeLookup.size == cr.args1.length + cr.args2.length)
    val fwp = new Array[Int](freeLookup.size)
    val assigners = mutable.ArrayBuffer.empty[PayloadAssigner]
    val lhsEmbId = cr.emb1.map(_.asInstanceOf[Ident].s).orNull
    val rhsEmbId = cr.emb2.map(_.asInstanceOf[Ident].s).orNull
    val embIdsUsed = mutable.HashSet.empty[String]
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
          emb match {
            case Some(IntLit(i)) => assigners += new IntConstAssigner(cellIdx, i)
            case Some(StringLit(s)) => assigners += new RefConstAssigner(cellIdx, s)
            case Some(e @ Ident(id)) if id == lhsEmbId =>
              assigners += (sym.payloadType match {
                case PayloadType.INT => new IntLHSMover(cellIdx)
                case PayloadType.REF =>
                  if(embIdsUsed.contains(lhsEmbId)) sys.error(s"Invalid payload expression ${e.show} in ${cr.show}: Value can only be moved, not copied")
                  embIdsUsed += lhsEmbId
                  new RefLHSMover(cellIdx)
                case PayloadType.LABEL => new LabelLHSAssigner(cellIdx)
              })
            case Some(e @ Ident(id)) if id == rhsEmbId =>
              assigners += (sym.payloadType match {
                case PayloadType.INT => new IntRHSMover(cellIdx)
                case PayloadType.REF =>
                  if(embIdsUsed.contains(rhsEmbId)) sys.error(s"Invalid payload expression ${e.show} in ${cr.show}: Value can only be moved, not copied")
                  embIdsUsed += rhsEmbId
                  new RefRHSMover(cellIdx)
                case PayloadType.LABEL => new LabelRHSAssigner(cellIdx)
              })
            case Some(e @ Ident(id)) =>
              cellEmbIds.get(id) match {
                case Some(cells) =>
                  sys.error(s"Invalid payload expression ${e.show} in ${cr.show}: Duplicate use of variable")
                case None =>
                  assert(e.sym.payloadType.canCopy)
                  cellEmbIds.put(id, ArrayBuffer(cellIdx))
              }
            case Some(e: EmbeddedApply) =>
              val ec = EmbeddedComputation[Int](cl, e)(cr.show) { a =>
                if(a.id == lhsEmbId) {
                  if(lhsPayloadType == PayloadType.REF) {
                    if(embIdsUsed.contains(lhsEmbId)) sys.error(s"Invalid payload expression ${e.show} in ${cr.show}: Value can only be moved, not copied")
                    embIdsUsed += lhsEmbId
                  }
                  -1
                } else if(a.id == rhsEmbId) {
                  if(rhsPayloadType == PayloadType.REF) {
                    if(embIdsUsed.contains(rhsEmbId)) sys.error(s"Invalid payload expression ${e.show} in ${cr.show}: Value can only be moved, not copied")
                    embIdsUsed += rhsEmbId
                  }
                  -2
                } else sys.error(s"Invalid payload expression ${e.show} in ${cr.show}")
              }
              assigners += new EmbeddedComputationAssigner(cellIdx, ec)
            case Some(e) =>
              sys.error(s"Invalid payload expression ${e.show} in ${cr.show}")
            case None =>
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
      if((refAs.distinct.length != refAs.length) || refAs.exists(embIdsUsed.contains))
        sys.error(s"Non-linear use of ref in embedded expression ${ee.show} in rule ${cr.show}")
      embIdsUsed ++= refAs
      ec
    }
    val cond = red.cond.map { ee => EmbeddedComputation(cl, ee)(cr.show)(s => cellEmbIds(s.id).head) }
    new GenericRuleBranch(cr.sym1.arity, cells.toArray, conns.toArray, fwp, assigners.toArray, embComp, cond)
  }
}

final class GenericRule(val sym1: Symbol, val sym2: Symbol, val branches: Seq[GenericRuleBranch]) {
  def symFor(rhs: Boolean): Symbol = if(rhs) sym2 else sym1
  def arity1: Int = sym1.arity
  def arity2: Int = sym2.arity
  def maxCells: Int = branches.iterator.map(_.cells.length).max
  def maxWires: Int = branches.iterator.map(b => b.connectionsPacked.length + b.freeWiresPacked.length).max

  def log(): Unit = {
    println(s"Rule ${sym1.id} ${sym2.id}")
    branches.foreach(_.log())
  }

  override def toString: String = s"$sym1 . $sym2"
}

object GenericRule {
  def apply[C](cl: ClassLoader, cr: CheckedRule): GenericRule = cr match {
    case dr: DerivedRule if dr.sym1.id == "erase" => deriveErase(cl, dr.sym2, dr.sym1)
    case dr: DerivedRule if dr.sym1.id == "dup" => deriveDup(cl, dr.sym2, dr.sym1)
    case cr: MatchRule => apply(cl, cr)
  }

  def apply[C](cl: ClassLoader, cr: MatchRule): GenericRule =
    new GenericRule(cr.sym1, cr.sym2, cr.reduction.map(r => GenericRuleBranch(cl, cr, r)))

  def deriveErase(cl: ClassLoader, sym: Symbol, eraseSym: Symbol): GenericRule = {
    val cells = Array.fill(sym.arity)(eraseSym)
    val fwp = (0 until sym.arity).map(i => checkedIntOfShorts(i, -1)).toArray
    val embComp = sym.payloadType match {
      case PayloadType.REF => Seq(new EmbeddedMethodApplication(cl, classOf[Intrinsics.type].getName, "eraseRef", Nil, Array(-2), null))
      case _ => Nil
    }
    new GenericRule(eraseSym, sym, Seq(new GenericRuleBranch(0, cells, Array.empty, fwp, Array(), embComp, None)))
  }

  def deriveDup(cl: ClassLoader, sym: Symbol, dupSym: Symbol): GenericRule = {
    if(sym == dupSym)
      new GenericRule(dupSym, sym, Seq(new GenericRuleBranch(2, Array.empty, Array.empty, Array(checkedIntOfShorts(-3, -1), checkedIntOfShorts(-4, -1)), Array(), Nil, None)))
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
        case PayloadType.REF => Seq(new EmbeddedMethodApplication(cl, classOf[Intrinsics.type].getName, "dupRef", Nil, Array(-2, sym.arity, sym.arity+1), null))
        case _ => Nil
      }
      new GenericRule(dupSym, sym, Seq(new GenericRuleBranch(2, cells, conns, fwp1 ++ fwp2, Array(), embComp, None)))
    }
  }
}

abstract class RuleImplFactory[T] {
  def apply(lookup: SymbolIdLookup): T
}

trait SymbolIdLookup {
  def getSymbolId(name: String): Int
}
