package de.szeiger.interact.stc1

import de.szeiger.interact.codegen.{ClassWriter, LocalClassLoader}
import de.szeiger.interact._
import de.szeiger.interact.ast.{CompilationUnit, Symbol, Symbols}

import java.util.Arrays
import scala.collection.mutable

abstract class Cell {
  def arity: Int
  def auxCell(p: Int): Cell
  def auxPort(p: Int): Int
  def setAux(p: Int, c2: Cell, p2: Int): Unit
  def reduce(c: Cell, ptw: Interpreter): Unit
  def cellSymbol: Symbol
}

final class DynamicCell(val cellSymbol: Symbol, val arity: Int) extends Cell {
  private[this] final val auxCells = new Array[Cell](arity)
  private[this] final val auxPorts = new Array[Int](arity)
  def auxCell(p: Int): Cell = auxCells(p)
  def auxPort(p: Int): Int = auxPorts(p)
  def setAux(p: Int, c2: Cell, p2: Int): Unit = { auxCells(p) = c2; auxPorts(p) = p2 }
  def reduce(c: Cell, ptw: Interpreter): Unit = ()
}

abstract class InitialRuleImpl {
  def reduce(a0: Cell, a1: Cell, ptw: Interpreter): Unit
  def freeWires: Array[Symbol]
}

final class Interpreter(globals: Symbols, compilationUnit: CompilationUnit, config: Config) extends BaseInterpreter { self =>
  private[this] val initialRuleImpls: Vector[InitialRuleImpl] = {
    val lcl = new LocalClassLoader
    val cw = ClassWriter(config, lcl)
    val initial = new CodeGen("generated", cw, config, compilationUnit, globals).compile()
    cw.close()
    initial.map { cln => lcl.loadClass(cln).getDeclaredConstructor().newInstance().asInstanceOf[InitialRuleImpl] }
  }
  private[this] val cutBuffer, irreducible = new CutBuffer(16)
  private[this] val freeWires = mutable.HashSet.empty[Cell]
  private[this] var metrics: ExecutionMetrics = _
  private[this] var active0, active1: Cell = _

  def getMetrics: ExecutionMetrics = metrics

  def getAnalyzer: Analyzer[Cell] = new Analyzer[Cell] {
    val principals = (cutBuffer.iterator ++ irreducible.iterator).flatMap { case (c1, c2) => Seq((c1, c2), (c2, c1)) }.toMap
    def irreduciblePairs: IterableOnce[(Cell, Cell)] = irreducible.iterator
    def rootCells = (self.freeWires.iterator ++ principals.keysIterator).toSet
    def getSymbol(c: Cell): Symbol = Option(c.cellSymbol).getOrElse(Symbol.NoSymbol)
    def getConnected(c: Cell, port: Int): (Cell, Int) =
      if(port == -1) principals.get(c).map((_, -1)).orNull else (c.auxCell(port), c.auxPort(port))
    def isFreeWire(c: Cell): Boolean = c.isInstanceOf[DynamicCell] && c.cellSymbol.isDefined
  }

  def initData(): Unit = {
    cutBuffer.clear()
    irreducible.clear()
    freeWires.clear()
    if(config.collectStats) metrics = new ExecutionMetrics
    initialRuleImpls.foreach { rule =>
      val free = rule.freeWires.map(new DynamicCell(_, 1))
      freeWires.addAll(free)
      val lhs = new DynamicCell(Symbol.NoSymbol, freeWires.size)
      free.iterator.zipWithIndex.foreach { case (c, p) => lhs.setAux(p, c, 0) }
      rule.reduce(lhs, new DynamicCell(Symbol.NoSymbol, 0), this)
    }
    if(config.collectStats) metrics = new ExecutionMetrics
  }

  def dispose(): Unit = ()

  def reduce(): Unit =
    while(true) {
      while(active0 != null) {
        val a0 = active0
        active0 = null
        a0.reduce(active1, this)
      }
      if(cutBuffer.isEmpty) return
      val (a0, a1) = cutBuffer.pop()
      a0.reduce(a1, this)
    }

  // ptw methods:

  def addActive(a0: Cell, a1: Cell): Unit =
    if(active0 == null) { active0 = a0; active1 = a1 } else cutBuffer.addOne(a0, a1)

  def addIrreducible(a0: Cell, a1: Cell): Unit = irreducible.addOne(a0, a1)

  def recordStats(steps: Int, cellAllocations: Int, cachedCellReuse: Int, singletonUse: Int, loopSave: Int, labelCreate: Int): Unit =
    metrics.recordStats(steps, cellAllocations, 0, cachedCellReuse, singletonUse, 0, loopSave, 0, 0, labelCreate)

  def recordMetric(metric: String, inc: Int): Unit = metrics.recordMetric(metric, inc)
}


final class CutBuffer(initialSize: Int) {
  private[this] var pairs = new Array[Cell](initialSize*2)
  private[this] var len = 0
  @inline def addOne(c1: Cell, c2: Cell): Unit = {
    if(len == pairs.length)
      pairs = Arrays.copyOf(pairs, pairs.length*2)
    pairs(len) = c1
    pairs(len+1) = c2
    len += 2
  }
  @inline def isEmpty: Boolean = len == 0
  @inline def pop(): (Cell, Cell) = {
    len -= 2
    val c1 = pairs(len)
    val c2 = pairs(len+1)
    pairs(len) = null
    pairs(len+1) = null
    (c1, c2)
  }
  def clear(): Unit =
    if(len > 0) {
      pairs = new Array[Cell](initialSize * 2)
      len = 0
    }
  def iterator: Iterator[(Cell, Cell)] = pairs.iterator.take(len).grouped(2).map { case Seq(c1, c2) => (c1, c2) }
}
