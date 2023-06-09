package de.szeiger.interact.st3

import de.szeiger.interact.codegen.{LocalClassLoader, ParSupport}
import de.szeiger.interact.{Analyzer, CheckedRule, BaseInterpreter, GenericRuleImpl, Symbol, SymbolIdLookup, Symbols}
import de.szeiger.interact.mt.BitOps._

import java.util.Arrays
import scala.annotation.{switch, tailrec}
import scala.collection.mutable

abstract class Cell(final var symId: Int, _pcell: Cell, _pport: Int) {
  final var pcell: Cell = _pcell
  final var pport: Int = _pport

  def arity: Int
  def auxCell(p: Int): Cell
  def auxPort(p: Int): Int
  def setAux(p: Int, c2: Cell, p2: Int): Unit
  def setCell(p: Int, c2: Cell, p2: Int): Unit
  def getCell(p: Int): Cell
  def getPort(p: Int): Int

  final def allPorts: Iterator[(Cell, Int)] = (-1 until arity).iterator.map(i => (getCell(i), getPort(i)))
  override def toString = s"Cell($symId, $arity, ${allPorts.map { w => s"(${if(w._1 == null) "null" else "_"})" }.mkString(", ") })@${System.identityHashCode(this)}"
}

class Cell0(_symId: Int, _pcell: Cell, _pport: Int) extends Cell(_symId, _pcell, _pport) {
  def this(_symId: Int) = this(_symId, null, 0)
  final def arity: Int = 0
  final def auxCell(p: Int): Cell = null
  final def auxPort(p: Int): Int = 0
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = ()
  final def setCell(p: Int, c2: Cell, p2: Int): Unit = { pcell = c2; pport = p2 }
  final def getCell(p: Int): Cell = pcell
  final def getPort(p: Int): Int = pport
}

class Cell1(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int) extends Cell(_symId, _pcell, _pport) {
  def this(_symId: Int) = this(_symId, null, 0, null, 0)
  final var acell0: Cell = _acell0
  final var aport0: Int = _aport0
  final def arity: Int = 1
  final def auxCell(p: Int): Cell = acell0
  final def auxPort(p: Int): Int = aport0
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = { acell0 = c2; aport0 = p2 }
  final def setCell(p: Int, c2: Cell, p2: Int): Unit = if(p == 0) { acell0 = c2; aport0 = p2 } else { pcell = c2; pport = p2 }
  final def getCell(p: Int): Cell = if(p == 0) acell0 else pcell
  final def getPort(p: Int): Int = if(p == 0) aport0 else pport
}

class Cell2(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int, _acell1: Cell, _aport1: Int) extends Cell(_symId, _pcell, _pport) {
  def this(_symId: Int) = this(_symId, null, 0, null, 0, null, 0)
  final var acell0: Cell = _acell0
  final var aport0: Int = _aport0
  final var acell1: Cell = _acell1
  final var aport1: Int = _aport1
  final def arity: Int = 2
  final def auxCell(p: Int): Cell = if(p == 0) acell0 else acell1
  final def auxPort(p: Int): Int = if(p == 0) aport0 else aport1
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = if(p == 0) { acell0 = c2; aport0 = p2 } else { acell1 = c2; aport1 = p2 }
  final def setCell(p: Int, c2: Cell, p2: Int): Unit = (p: @switch) match {
    case 0 => acell0 = c2; aport0 = p2
    case 1 => acell1 = c2; aport1 = p2
    case _ => pcell = c2; pport = p2
  }
  final def getCell(p: Int): Cell = (p: @switch) match {
    case 0 => acell0
    case 1 => acell1
    case _ => pcell
  }
  final def getPort(p: Int): Int = (p: @switch) match {
    case 0 => aport0
    case 1 => aport1
    case _ => pport
  }
}

class CellN(_symId: Int, val arity: Int, _pcell: Cell, _pport: Int) extends Cell(_symId, _pcell, _pport) {
  def this(_symId: Int, _arity: Int) = this(_symId, _arity, null, 0)
  private[this] final val auxCells = new Array[Cell](arity)
  private[this] final val auxPorts = new Array[Int](arity)
  final def auxCell(p: Int): Cell = auxCells(p)
  final def auxPort(p: Int): Int = auxPorts(p)
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = { auxCells(p) = c2; auxPorts(p) = p2 }
  final def setCell(p: Int, c2: Cell, p2: Int): Unit =
    if(p < 0) { pcell = c2; pport = p2 } else { auxCells(p) = c2; auxPorts(p) = p2 }
  final def getCell(p: Int): Cell = if(p < 0) pcell else auxCells(p)
  final def getPort(p: Int): Int = if(p < 0) pport else auxPorts(p)
}

object Cells {
  @inline def mk(symId: Int, arity: Int): Cell = arity match {
    case 0 => new Cell0(symId)
    case 1 => new Cell1(symId)
    case 2 => new Cell2(symId)
    case _ => new CellN(symId, arity)
  }
}

class WireCell(final val sym: Symbol, _symId: Int) extends Cell0(_symId) {
  override def toString = s"WireCell($sym, $symId, ${allPorts.map { w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
}

abstract class RuleImpl {
  var rule: GenericRuleImpl = _
  def reduce(cut: Cell, ptw: PerThreadWorker): Unit
  def cellAllocationCount: Int
}

final class InterpretedRuleImpl(s1id: Int, protoCells: Array[Int], freeWiresPorts: Array[Int], connections: Array[Int]) extends RuleImpl {
  override def toString = rule.toString

  private[this] def delay(nanos: Int): Unit = {
    val end = System.nanoTime() + nanos
    while(System.nanoTime() < end) Thread.onSpinWait()
  }

  def reduce(cell: Cell, ptw: PerThreadWorker): Unit = {
    val (c1, c2) = if(cell.symId == s1id) (cell, cell.pcell) else (cell.pcell, cell)
    val cells = ptw.tempCells
    val cccells = ptw.cutCacheCells
    val ccports = ptw.cutCachePorts
    //delay(20)
    var i = 0
    while(i < protoCells.length) {
      val pc = protoCells(i)
      val sid = short0(pc)
      val ari = short1(pc)
      cells(i) = Cells.mk(sid, ari)
      i += 1
    }

    i = 0
    while(i < c1.arity) {
      cccells(i) = c1.auxCell(i)
      ccports(i) = c1.auxPort(i)
      i += 1
    }
    i = 0
    while(i < c2.arity) {
      cccells(i + c1.arity) = c2.auxCell(i)
      ccports(i + c1.arity) = c2.auxPort(i)
      i += 1
    }

    // Connect cut wire to new cell
    @inline def connectFreeToInternal(ct1: Int, p1: Int, ct2: Int): Unit = {
      val c2 = cccells(ct2)
      val p2 = ccports(ct2)
      val c1 = cells(ct1)
      c1.setCell(p1, c2, p2)
      c2.setCell(p2, c1, p1)
      if((p1 & p2) < 0) ptw.createCut(c1)
    }

    @inline def connectFreeToFree(ct1: Int, ct2: Int): Unit = {
      val c1 = cccells(ct1)
      val p1 = ccports(ct1)
      val c2 = cccells(ct2)
      val p2 = ccports(ct2)
      c1.setCell(p1, c2, p2)
      c2.setCell(p2, c1, p1)
      if((p1 & p2) < 0) ptw.createCut(c1)
    }

    i = 0
    while(i < freeWiresPorts.length) {
      val fwp = freeWiresPorts(i)
      val fw = short0(fwp)
      if(fw >= 0) connectFreeToInternal(fw, short1(fwp), i)
      else if(i < -1-fw) connectFreeToFree(i, -1-fw)
      i += 1
    }

    i = 0
    while(i < connections.length) {
      val conn = connections(i)
      val c1 = cells(byte0(conn))
      val p1 = byte1(conn)
      val c2 = cells(byte2(conn))
      val p2 = byte3(conn)
      c1.setCell(p1, c2, p2)
      c2.setCell(p2, c1, p1)
      if((p1 & p2) < 0) ptw.createCut(c1)
      i += 1
    }
  }

  def cellAllocationCount: Int = protoCells.length
}

final class Interpreter(globals: Symbols, rules: Iterable[CheckedRule], compile: Boolean,
  debugLog: Boolean, debugBytecode: Boolean, val collectStats: Boolean) extends BaseInterpreter with SymbolIdLookup { self =>
  final val scope: Analyzer[Cell] = new Analyzer[Cell] {
    def createCell(sym: Symbol): Cell = if(sym.isCons) Cells.mk(getSymbolId(sym), sym.arity) else new WireCell(sym, 0)
    def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit = {
      c1.setCell(p1, c2, p2)
      c2.setCell(p2, c1, p1)
    }
    def getSymbol(c: Cell): Symbol = c match {
      case c: WireCell => c.sym
      case c => reverseSymIds(c.symId)
    }
    def getConnected(c: Cell, port: Int): (Cell, Int) = (c.getCell(port), c.getPort(port))
    def isFreeWire(c: Cell): Boolean = c.isInstanceOf[WireCell]
  }
  private[this] final val allSymbols = globals.symbols
  private[this] final val symIds = mutable.HashMap.from[Symbol, Int](allSymbols.zipWithIndex.map { case (s, i) => (s, i+1) })
  private[this] final val reverseSymIds = symIds.iterator.map { case (k, v) => (v, k) }.toMap
  private[this] final val symBits = Integer.numberOfTrailingZeros(Integer.highestOneBit(symIds.size))+1
  final val (ruleImpls, maxRuleCells, maxArity) = createRuleImpls()

  def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)
  def getSymbolId(name: String): Int = getSymbolId(globals(name))
  def createTempCells(): Array[Cell] = new Array[Cell](maxRuleCells)
  def createCutCache(): (Array[Cell], Array[Int]) = (new Array[Cell](maxArity*2), new Array[Int](maxArity*2))

  def createRuleImpls(): (Array[RuleImpl], Int, Int) = {
    val (cl, codeGen) =
      if(compile) (new LocalClassLoader(), new CodeGen("de/szeiger/interact/st3/gen", debugBytecode))
      else (null, null)
    val ris = new Array[RuleImpl](1 << (symBits << 1))
    val maxC, maxA = new ParSupport.AtomicCounter
    ParSupport.foreach(rules) { cr =>
      val g = GenericRuleImpl(cr, globals)
      if(debugLog) g.log()
      val ri =
        if(compile) codeGen.compile(g, cl)(this)
        else {
          maxC.max(g.maxCells)
          maxA.max(g.arity1)
          maxA.max(g.arity2)
          new InterpretedRuleImpl(getSymbolId(g.sym1), g.cells.map(s => intOfShorts(getSymbolId(s), s.arity)), g.freeWiresPacked, g.connectionsPacked)
        }
      ri.rule = g
      ris(mkRuleKey(getSymbolId(g.sym1), getSymbolId(g.sym2))) = ri
    }
    (ris, maxC.get, maxA.get)
  }

  @inline def mkRuleKey(c: Cell): Int = mkRuleKey(c.symId, c.pcell.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  def detectInitialCuts: CutBuffer = {
    val detected = mutable.HashSet.empty[Cell]
    val buf = new CutBuffer(16)
    scope.reachableCells.foreach { c =>
      val ri = ruleImpls(mkRuleKey(c))
      if(ri != null) {
        if(c.pport < 0 && c.pcell.pport < 0 && !detected.contains(c.pcell)) {
          detected.addOne(c)
          buf.addOne(c, ri)
        }
      }
    }
    buf
  }

  // Used by the debugger
  def getRuleImpl(c: Cell): RuleImpl = ruleImpls(mkRuleKey(c))
  def reduce1(c: Cell): Unit = {
    val w = new PerThreadWorker(this) {
      protected[this] override def enqueueCut(c: Cell, ri: RuleImpl): Unit = ()
    }
    w.setNext(c, getRuleImpl(c))
    w.processNext()
  }

  def reduce(): Int = {
    val initial = detectInitialCuts
    val w = new PerThreadWorker(this) {
      protected[this] override def enqueueCut(c: Cell, ri: RuleImpl): Unit = initial.addOne(c, ri)
    }
    while(initial.nonEmpty) {
      val (wr, ri) = initial.pop()
      w.setNext(wr, ri)
      w.processAll()
    }
    if(collectStats)
      println(s"Total steps: ${w.steps}, allocated cells: ${w.cellAllocations}")
    w.steps
  }
}

final class CutBuffer(initialSize: Int) {
  private[this] var wrs = new Array[Cell](initialSize)
  private[this] var ris = new Array[RuleImpl](initialSize)
  private[this] var len = 0
  @inline def addOne(wr: Cell, ri: RuleImpl): Unit = {
    if(len == wrs.length) {
      wrs = Arrays.copyOf(wrs, wrs.length*2)
      ris = Arrays.copyOf(ris, ris.length*2)
    }
    wrs(len) = wr
    ris(len) = ri
    len += 1
  }
  @inline def nonEmpty: Boolean = len != 0
  @inline def pop(): (Cell, RuleImpl) = {
    len -= 1
    val wr = wrs(len)
    val ri = ris(len)
    wrs(len) = null
    (wr, ri)
  }
}

abstract class PerThreadWorker(final val inter: Interpreter) {
  final val tempCells = inter.createTempCells()
  final val (cutCacheCells, cutCachePorts) = inter.createCutCache()
  private[this] final var nextCut: Cell = _
  private[this] final var nextRule: RuleImpl = _
  private[this] final val collectStats = inter.collectStats
  var steps, cellAllocations = 0

  protected[this] def enqueueCut(c: Cell, ri: RuleImpl): Unit

  final def createCut(c: Cell): Unit = {
    val ri = inter.ruleImpls(inter.mkRuleKey(c))
    if(ri != null) {
      if(nextCut == null) { nextCut = c; nextRule = ri }
      else enqueueCut(c, ri)
    }
  }

  final def setNext(c: Cell, ri: RuleImpl): Unit = {
    this.nextCut = c
    this.nextRule = ri
  }

  final def processNext(): Unit = {
    val c = nextCut
    val ri = nextRule
    nextCut = null
    ri.reduce(c, this)
    if(collectStats) {
      steps += 1
      cellAllocations += ri.cellAllocationCount
    }
  }

  @tailrec
  final def processAll(): Unit = {
    processNext()
    if(nextCut != null) processAll()
  }
}
