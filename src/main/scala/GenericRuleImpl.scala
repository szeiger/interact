package de.szeiger.interact

import de.szeiger.interact.mt.BitOps._

import scala.collection.mutable

case class Connection(c1: Idx, c2: Idx) { def str = s"${c1.str} <-> ${c2.str}" }

sealed abstract class Idx { def str: String }
case class CellIdx(idx: Int, port: Int) extends Idx { def str = s"c$idx:$port" }
case class FreeIdx(rhs: Boolean, idx: Int) extends Idx { def str = if(rhs) s"rhs:$idx" else s"lhs:$idx" }

final class GenericRuleImpl(val cells: Array[(Symbol, Int)], val connectionsPacked: Array[Int],
  val arity1: Int, val arity2: Int, val freeWiresPacked: Array[Int]) {

  lazy val (freeWiresPacked1, freWiresPacked2) = freeWiresPacked.splitAt(arity1)

  private[this] def mkFreeIdx(idx: Int): FreeIdx = {
    val rhs = idx >= arity1
    FreeIdx(rhs, if(rhs) idx-arity1 else idx)
  }
  private[this] def mkIdx(t: Int, p: Int): Idx =
    if(t >= 0) CellIdx(t, p) else mkFreeIdx(-1-t)

  def internalConns: Iterator[Connection] = connectionsPacked.iterator.map { i =>
    Connection(mkIdx(byte0(i), byte1(i)), mkIdx(byte2(i), byte3(i)))
  }

  def wireConns: Iterator[Connection] = freeWiresPacked.zipWithIndex.iterator.map { case (fw, idx) =>
    Connection(mkFreeIdx(idx), mkIdx(short0(fw), short1(fw)))
  }

  def maxCells: Int = cells.length
  def maxWires: Int = connectionsPacked.length + freeWiresPacked.length

  def log(): Unit = {
    println("  Cells:")
    cells.zipWithIndex.foreach { case ((sym, arity), idx) => println(s"    [$idx] $sym $arity") }
    println("  Connections:")
    (internalConns ++ wireConns).foreach { c => println(s"    ${c.str}") }
  }
}

object GenericRuleImpl {
  def apply[C >: Null <: AnyRef](scope: Scope[C], reduced: Seq[AST.Cut], globals: Symbols, args1: Seq[AST.Ident], args2: Seq[AST.Ident]): GenericRuleImpl = {
    //println(s"***** Preparing ${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}")
    val syms = new Symbols(Some(globals))
    val sc = new scope.Delegate
    sc.add(reduced, syms)
    //sc.validate()
    val cells = sc.reachableCells.filter(c => !sc.freeWires.contains(c)).toIndexedSeq
    val protoCells = cells.iterator.map { c => (scope.getSymbol(c), scope.getArity(c)) }.toArray
    val freeLookup = sc.freeWires.iterator.map { w => (scope.getSymbol(w), w) }.toMap
    val wires = (args1 ++ args2).map { i => freeLookup(syms(i)) }.toIndexedSeq
    val lookup = (cells.iterator.zipWithIndex ++ wires.iterator.zipWithIndex.map { case (w, p) => (w, -p-1) }).toMap
    val conns = mutable.HashSet.empty[Int]
    cells.iterator.zipWithIndex.foreach { case (c, i) =>
      scope.getAllConnected(c).zipWithIndex.foreach { case ((t, p), j) =>
        val w = lookup(t)
        if(w >= 0 && !conns.contains(checkedIntOfBytes(w, p, i, j-1)))
          conns.add(checkedIntOfBytes(i, j-1, w, p))
      }
    }
    val fwp = wires.iterator.map { w => val (c, p) = scope.getConnected(w, -1); checkedIntOfShorts(lookup(c), p) }.toArray
    new GenericRuleImpl(protoCells, conns.toArray, args1.length, args2.length, fwp)
  }
}
