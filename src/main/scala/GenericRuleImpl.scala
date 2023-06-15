package de.szeiger.interact

import de.szeiger.interact.mt.BitOps._

import java.lang.invoke.{MethodHandle, MethodHandles}
import java.lang.reflect.Modifier
import scala.collection.mutable

case class Connection(c1: Idx, c2: Idx) { def str = s"${c1.str} <-> ${c2.str}" }

sealed abstract class Idx { def str: String }
case class CellIdx(idx: Int, port: Int) extends Idx { def str = s"c$idx:$port" }
case class FreeIdx(rhs: Boolean, idx: Int) extends Idx { def str = if(rhs) s"rhs:$idx" else s"lhs:$idx" }

trait IntBox { def getValue: Int; def setValue(i: Int): Unit }
trait RefBox { def getValue: AnyRef; def setValue(o: AnyRef): Unit }
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

final class EmbeddedComputation[A](cls: String, method: String, consts: Iterable[(Int, Any)], val argIndices: A) {
  def getMethod(cl: ClassLoader): MethodHandle = {
    val c = cl.loadClass(cls)
    val m = c.getMethods.find(_.getName == method).getOrElse(sys.error(s"Method $method not found in $cls"))
    var mh = MethodHandles.lookup().unreflect(m)
    if(!Modifier.isStatic(m.getModifiers)) mh = MethodHandles.insertArguments(mh, 0, c.getField("MODULE$").get(null))
    for((pos, v) <- consts) mh = MethodHandles.insertArguments(mh, pos, v)
    mh
  }
}

object EmbeddedComputation {
  def apply[A](e: AST.EmbeddedExpr)(creator: => String)(handleArgs: IndexedSeq[String] => A): EmbeddedComputation[A] = e match {
    case emb @ AST.EmbeddedAp(_, args) =>
      val consts = mutable.ArrayBuffer.empty[(Int, Any)]
      val vars = mutable.ArrayBuffer.empty[String]
      var offset = 0
      args.zipWithIndex.foreach {
        case (AST.EmbeddedInt(v), i) =>
          consts += ((i-offset, v))
          offset += 1
        case (AST.EmbeddedString(v), i) =>
          consts += ((i-offset, v))
          offset += 1
        case (AST.EmbeddedIdent(id), _) =>
          vars += id
        case (e, _) =>
          sys.error(s"Argument $e of embedded computation must be a literal or variable in $creator")
      }
      new EmbeddedComputation(emb.className, emb.methodName, consts, handleArgs(vars.toIndexedSeq))
    case _ => sys.error(s"Embedded computation must be a method call in $creator")

  }
}

final class GenericRuleImpl(val sym1: Symbol, val sym2: Symbol,
  val cells: Array[Symbol], val connectionsPacked: Array[Int],
  val freeWiresPacked: Array[Int],
  val assigners: Array[PayloadAssigner],
  val embeddedComps: Seq[EmbeddedComputation[Array[Int]]]) {

  def symFor(rhs: Boolean): Symbol = if(rhs) sym2 else sym1
  def arity1: Int = sym1.arity
  def arity2: Int = sym2.arity
  def maxCells: Int = cells.length
  def maxWires: Int = connectionsPacked.length + freeWiresPacked.length
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
    println(s"Rule ${sym1.id} ${sym2.id}")
    println("  Cells:")
    cells.zipWithIndex.foreach { case (sym, idx) => println(s"    [$idx] $sym ${sym.arity}") }
    println("  Connections:")
    (internalConns ++ wireConnsDistinct).foreach { c => println(s"    ${c.str}") }
  }

  override def toString: String = s"$sym1 . $sym2"
}

object GenericRuleImpl {
  def apply[C](cr: CheckedRule, globals: Symbols): GenericRuleImpl = cr match {
    case dr: DerivedRule if dr.name1 == "erase" => deriveErase(dr.name2, globals)
    case dr: DerivedRule if dr.name1 == "dup" => deriveDup(dr.name2, globals)
    case cr: CheckedMatchRule => apply(cr, globals)
  }

  def apply[C](cr: CheckedMatchRule, globals: Symbols): GenericRuleImpl = {
    //println(s"***** Preparing ${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}")
    val syms = new Symbols(Some(globals))
    val cells = mutable.ArrayBuffer.empty[Symbol]
    val conns = mutable.HashSet.empty[Int]
    val freeLookup = (cr.args1.iterator ++ cr.args2.iterator).zipWithIndex.map { case (n, i) => (syms.getOrAdd(n), -i-1) }.toMap
    assert(freeLookup.size == cr.args1.length + cr.args2.length)
    val fwp = new Array[Int](freeLookup.size)
    val assigners = mutable.ArrayBuffer.empty[PayloadAssigner]
    val lhsEmbId = cr.emb1.map(_.s).orNull
    val rhsEmbId = cr.emb2.map(_.s).orNull
    val embIdsUsed = mutable.HashSet.empty[String]
    val cellEmbIds = mutable.HashMap.empty[String, Int]
    val shouldUseEmbIds = mutable.HashSet.empty[String]
    if(globals(cr.name1).payloadType == PayloadType.REF) shouldUseEmbIds += (if(lhsEmbId != null) lhsEmbId else "$unnamedLHS")
    if(globals(cr.name2).payloadType == PayloadType.REF) shouldUseEmbIds += (if(rhsEmbId != null) rhsEmbId else "$unnamedRHS")
    if(lhsEmbId != null) cellEmbIds.put(lhsEmbId, -1)
    if(rhsEmbId != null) cellEmbIds.put(rhsEmbId, -2)
    val sc = new Scope[Int] {
      override def createCell(sym: Symbol, emb: Option[AST.EmbeddedExpr]): Int = {
        if(sym.isCons) {
          val cellIdx = cells.length
          cells += sym
          var embId: String = null
          emb match {
            case Some(AST.EmbeddedInt(i)) => assigners += new IntConstAssigner(cellIdx, i)
            case Some(AST.EmbeddedString(s)) => assigners += new RefConstAssigner(cellIdx, s)
            case Some(e @ AST.EmbeddedIdent(id)) if id == lhsEmbId =>
              if(embIdsUsed.contains(lhsEmbId)) sys.error(s"Invalid payload expression ${e.show} in ${cr.show}: Value can only be moved, not copied")
              embIdsUsed += lhsEmbId
              assigners += (sym.payloadType match {
                case PayloadType.INT => new IntLHSMover(cellIdx)
                case PayloadType.REF => new RefLHSMover(cellIdx)
              })
            case Some(e @ AST.EmbeddedIdent(id)) if id == rhsEmbId =>
              if(embIdsUsed.contains(rhsEmbId)) sys.error(s"Invalid payload expression ${e.show} in ${cr.show}: Value can only be moved, not copied")
              embIdsUsed += rhsEmbId
              assigners += (sym.payloadType match {
                case PayloadType.INT => new IntRHSMover(cellIdx)
                case PayloadType.REF => new RefRHSMover(cellIdx)
              })
            case Some(e @ AST.EmbeddedIdent(id)) =>
              embId = id
              if(cellEmbIds.put(id, cellIdx).isDefined)
                sys.error(s"Invalid payload expression ${e.show} in ${cr.show}: Duplicate use of variable")
            case Some(e) =>
              sys.error(s"Invalid payload expression ${e.show} in ${cr.show}")
            case None =>
              embId = "$unnamedCell" + cellIdx
          }
          if(sym.hasPayload && embId != null) shouldUseEmbIds += embId
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
    sc.addExprs(cr.connected, syms)
    val embComp = cr.embRed.map { ee =>
      EmbeddedComputation(ee)(cr.show) { as =>
        if((as.distinct.length != as.length) || as.exists(embIdsUsed.contains(_)))
          sys.error(s"Non-linear variable use in embedded method call ${ee.show} in rule ${cr.show}")
        embIdsUsed ++= as
        as.map(cellEmbIds).toArray
      }
    }
    val unusedEmbIds = shouldUseEmbIds -- embIdsUsed
    if(unusedEmbIds.nonEmpty) sys.error(s"Unused variable(s) ${unusedEmbIds.mkString(", ")} in rule ${cr.show}")
    new GenericRuleImpl(globals(cr.name1), globals(cr.name2), cells.toArray, conns.toArray, fwp, assigners.toArray, embComp)
  }

  def deriveErase(name: String, globals: Symbols): GenericRuleImpl = {
    val sym = globals(name)
    val eraseSym = globals("erase")
    val cells = Array.fill(sym.arity)(eraseSym)
    val fwp = (0 until sym.arity).map(i => checkedIntOfShorts(i, -1)).toArray
    val embComp = sym.payloadType match {
      case PayloadType.REF => Seq(new EmbeddedComputation(classOf[Intrinsics.type].getName, "eraseRef", Nil, Array(-2)))
      case _ => Nil
    }
    new GenericRuleImpl(eraseSym, sym, cells, Array.empty, fwp, Array(), embComp)
  }

  def deriveDup(name: String, globals: Symbols): GenericRuleImpl = {
    val sym = globals(name)
    val dupSym = globals("dup")
    if(name == "dup")
      new GenericRuleImpl(dupSym, sym, Array.empty, Array.empty, Array(checkedIntOfShorts(-3, -1), checkedIntOfShorts(-4, -1)), Array(), Nil)
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
        case PayloadType.REF => Seq(new EmbeddedComputation(classOf[Intrinsics.type].getName, "dupRef", Nil, Array(-2, sym.arity, sym.arity+1)))
        case _ => Nil
      }
      new GenericRuleImpl(dupSym, sym, cells, conns, fwp1 ++ fwp2, Array(), embComp)
    }
  }
}

abstract class RuleImplFactory[T] {
  def apply(lookup: SymbolIdLookup): T
}

trait SymbolIdLookup {
  def getSymbolId(name: String): Int
}
