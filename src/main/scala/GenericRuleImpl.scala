package de.szeiger.interact

import de.szeiger.interact.mt.BitOps._

import scala.collection.mutable

case class Connection(c1: Idx, c2: Idx) { def str = s"${c1.str} <-> ${c2.str}" }

sealed abstract class Idx { def str: String }
case class CellIdx(idx: Int, port: Int) extends Idx { def str = s"c$idx:$port" }
case class FreeIdx(rhs: Boolean, idx: Int) extends Idx { def str = if(rhs) s"rhs:$idx" else s"lhs:$idx" }

final class GenericRuleImpl(val sym1: Symbol, val sym2: Symbol,
  val cells: Array[Symbol], val connectionsPacked: Array[Int],
  val freeWiresPacked: Array[Int]) {

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
    for(i <- 0 until cells.length) a(i) = new Array[Idx](cells(i).arity+1)
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
  def apply[C](cr: AnyCheckedRule, globals: Symbols): GenericRuleImpl = cr match {
    case dr: DerivedRule if dr.deriveName == "erase" => deriveErase(dr.otherName, globals)
    case dr: DerivedRule if dr.deriveName == "dup" => deriveDup(dr.otherName, globals)
    case cr: CheckedDefRule => apply(cr, globals)
  }

  def apply[C](cr: CheckedDefRule, globals: Symbols): GenericRuleImpl = {
    //println(s"***** Preparing ${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}")
    val syms = new Symbols(Some(globals))
    val cells = mutable.ArrayBuffer.empty[Symbol]
    val conns = mutable.HashSet.empty[Int]
    val freeLookup = (cr.args1.iterator ++ cr.args2.iterator).zipWithIndex.map { case (n, i) => (syms.getOrAdd(n), -i-1) }.toMap
    assert(freeLookup.size == cr.args1.length + cr.args2.length)
    val fwp = new Array[Int](freeLookup.size)
    val sc = new Scope[Int] {
      override def createCell(sym: Symbol): Int = if(sym.isCons) { cells += sym; cells.length-1 } else freeLookup(sym)
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
    new GenericRuleImpl(globals(cr.name1), globals(cr.name2), cells.toArray, conns.toArray, fwp)
  }

  def deriveErase(name: String, globals: Symbols): GenericRuleImpl = {
    val sym = globals(name)
    val eraseSym = globals("erase")
    val cells = Array.fill(sym.arity)(eraseSym)
    val fwp = (0 until sym.arity).map(i => checkedIntOfShorts(i, -1)).toArray
    new GenericRuleImpl(eraseSym, sym, cells, Array.empty, fwp)
  }

  def deriveDup(name: String, globals: Symbols): GenericRuleImpl = {
    val sym = globals(name)
    val dupSym = globals("dup")
    if(name == "dup")
      new GenericRuleImpl(dupSym, sym, Array.empty, Array.empty, Array(checkedIntOfShorts(-3, -1), checkedIntOfShorts(-4, -1)))
    else {
      val cells = Array.fill(sym.arity)(dupSym) ++ Array.fill(2)(sym)
      val conns = new Array[Int](sym.arity*2)
      for(i <- 0 until sym.arity) {
        conns(i*2) = checkedIntOfBytes(i, 0, sym.arity, i)
        conns(i*2+1) = checkedIntOfBytes(i, 1, sym.arity+1, i)
      }
      val fwp1 = Array[Int](checkedIntOfShorts(sym.arity, -1), checkedIntOfShorts(sym.arity+1, -1))
      val fwp2 = (0 until sym.arity).map(i => checkedIntOfShorts(i, -1)).toArray
      new GenericRuleImpl(dupSym, sym, cells, conns, fwp1 ++ fwp2)
    }
  }
}

abstract class RuleImplFactory[T] {
  def apply(lookup: SymbolIdLookup): T
}

trait SymbolIdLookup {
  def getSymbolId(name: String): Int
}
