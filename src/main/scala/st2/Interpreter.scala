package de.szeiger.interact.st2

import de.szeiger.interact.codegen.{CodeGen, RuleImplFactory, SymbolIdLookup}
import de.szeiger.interact.{AST, BaseInterpreter, CheckedRule, Connection, GenericRuleImpl, Idx, Scope, Symbol, Symbols}
import de.szeiger.interact.mt.BitOps._

import java.util.Arrays
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.annotation.{switch, tailrec}

final class WireRef(final var cell: Cell, final var cellPort: Int, _oppo: WireRef, _oppoCell: Cell, _oppoPort: Int) {
  def this(_c1: Cell, _p1: Int, _c2: Cell, _p2: Int) = this(_c1, _p1, null, _c2, _p2)

  if(cell != null) cell.setWireRef(cellPort, this)

  final val oppo: WireRef = if(_oppo != null) _oppo else new WireRef(_oppoCell, _oppoPort, this, null, 0)

  @inline def opposite: (Cell, Int) = (oppo.cell, oppo.cellPort)
}

abstract class Cell(final val symId: Int) {
  final var pref: WireRef = _

  def arity: Int
  def auxRef(p: Int): WireRef
  def setAuxRef(p: Int, wr: WireRef): Unit
  def setWireRef(p: Int, wr: WireRef): Unit
  def getWireRef(p: Int): WireRef
  def copy(): Cell

  final def getCell(p: Int): (Cell, Int) = {
    val w = getWireRef(p)
    if(w == null) null else w.opposite
  }
  final def allPorts: Iterator[WireRef] = (-1 until arity).iterator.map(getWireRef)
  final def allCells: Iterator[(WireRef, (Cell, Int))] = (-1 until arity).iterator.map { i => (getWireRef(i), getCell(i)) }
  override def toString = s"Cell($symId, $arity, ${allPorts.map { case w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
}

class Cell0(_symId: Int) extends Cell(_symId) {
  def arity: Int = 0
  def auxRef(p: Int): WireRef = null
  def setAuxRef(p: Int, wr: WireRef): Unit = ()
  def setWireRef(p: Int, wr: WireRef) = pref = wr
  def getWireRef(p: Int): WireRef = pref
  def copy() = new Cell0(symId)
}

class Cell1(_symId: Int) extends Cell(_symId) {
  final var aref0: WireRef = _
  def arity: Int = 1
  def auxRef(p: Int): WireRef = aref0
  def setAuxRef(p: Int, wr: WireRef): Unit = aref0 = wr
  def setWireRef(p: Int, wr: WireRef) = if(p == 0) aref0 = wr else pref = wr
  def getWireRef(p: Int): WireRef = if(p == 0) aref0 else pref
  def copy() = new Cell1(symId)
}

class Cell2(_symId: Int) extends Cell(_symId) {
  final var aref0: WireRef = _
  final var aref1: WireRef = _
  def arity: Int = 2
  def auxRef(p: Int): WireRef = if(p == 0) aref0 else aref1
  def setAuxRef(p: Int, wr: WireRef): Unit = if(p == 0) aref0 = wr else aref1 = wr
  def setWireRef(p: Int, wr: WireRef) = (p: @switch) match {
    case 0 => aref0 = wr
    case 1 => aref1 = wr
    case _ => pref = wr
  }
  def getWireRef(p: Int): WireRef = (p: @switch) match {
    case 0 => aref0
    case 1 => aref1
    case _ => pref
  }
  def copy() = new Cell2(symId)
}

class CellN(_symId: Int, val arity: Int) extends Cell(_symId) {
  private[this] final val auxRefs = new Array[WireRef](arity)
  def auxRef(p: Int): WireRef = auxRefs(p)
  def setAuxRef(p: Int, wr: WireRef): Unit = auxRefs(p) = wr
  def setWireRef(p: Int, wr: WireRef) =
    if(p < 0) pref = wr else auxRefs(p) = wr
  def getWireRef(p: Int): WireRef =
    if(p < 0) pref else auxRefs(p)
  def copy() = new CellN(symId, arity)
}

object Cells {
  @inline def mk(symId: Int, arity: Int): Cell = arity match {
    case 0 => new Cell0(symId)
    case 1 => new Cell1(symId)
    case 2 => new Cell2(symId)
    case _ => new CellN(symId, arity)
  }
  def getCell(c: Cell, p: Int): (Cell, Int) = {
      val w = c.getWireRef(p)
      if(w == null) null else w.opposite
    }
  def allPorts(c: Cell): Iterator[WireRef] = (-1 until c.arity).iterator.map(c.getWireRef)
  def allCells(c: Cell): Iterator[(WireRef, (Cell, Int))] = (-1 until c.arity).iterator.map { i => (c.getWireRef(i), getCell(c, i)) }
  def str(c: Cell) = c match {
    case c: WireCell => s"WireCell(${c.sym}, ${c.symId}, ${c.arity}, ${allPorts(c).map { case w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
    case c => s"Cell(${c.symId}, ${c.arity}, ${allPorts(c).map { case w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
  }
}

class WireCell(final val sym: Symbol, _symId: Int) extends Cell0(_symId) {
  override def toString = s"WireCell($sym, $symId, ${allPorts.map { case w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
}

abstract class RuleImpl {
  def reduce(wr: WireRef, ptw: PerThreadWorker): Unit
}

final class InterpretedRuleImpl(s1id: Int, protoCells: Array[Int], freeWiresPorts1: Array[Int], freeWiresPorts2: Array[Int], connections: Array[Int]) extends RuleImpl {
  private[this] def delay(nanos: Int): Unit = {
    val end = System.nanoTime() + nanos
    while(System.nanoTime() < end) Thread.onSpinWait()
  }

  def reduce(wr: WireRef, ptw: PerThreadWorker): Unit = {
    val (c1, c2) = if(wr.cell.symId == s1id) (wr.cell, wr.oppo.cell) else (wr.oppo.cell, wr.cell)
    val cells = ptw.tempCells
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
    while(i < connections.length) {
      val conn = connections(i)
      val t1 = cells(byte0(conn))
      val p1 = byte1(conn)
      val t2 = cells(byte2(conn))
      val p2 = byte3(conn)
      val w = new WireRef(t1, p1, t2, p2)
      if(p1 < 0 && p2 < 0) ptw.createCut(w)
      i += 1
    }

    @inline def cutTarget(i: Int) = if(i < c1.arity) c1.auxRef(i) else c2.auxRef(i-c1.arity)

    // Connect cut wire to new cell
    @inline def connectFreeToInternal(cIdx: Int, cp: Int, wr: WireRef): Unit =
      ptw.connect(wr, cells(cIdx), cp)

    // Connect 2 cut wires
    @inline def connectFreeToFree(wr1: WireRef, cutIdx2: Int): Unit = {
      val wr2 = cutTarget(cutIdx2)
      val (wt, wp) = wr1.opposite
      ptw.connect(wr2, wt, wp)
    }

    i = 0
    while(i < freeWiresPorts1.length) {
      val fwp = freeWiresPorts1(i)
      val fw = short0(fwp)
      if(fw >= 0) connectFreeToInternal(fw, short1(fwp), c1.auxRef(i))
      else if(i < -1-fw) connectFreeToFree(c1.auxRef(i), -1-fw)
      i += 1
    }
    i = 0
    while(i < freeWiresPorts2.length) {
      val fwp = freeWiresPorts2(i)
      val fw = short0(fwp)
      if(fw >= 0) connectFreeToInternal(fw, short1(fwp), c2.auxRef(i))
      else if(i+c1.arity < -1-fw) connectFreeToFree(c2.auxRef(i), -1-fw)
      i += 1
    }
  }
}

final class Dup0RuleImpl(derivedMainSymId: Int) extends RuleImpl {
  def reduce(wr: WireRef, ptw: PerThreadWorker): Unit = {
    val c1 = wr.cell
    val c2 = wr.oppo.cell
    val (cDup, cCons) = if(c1.symId == derivedMainSymId) (c1, c2) else (c2, c1)
    val wrA = cDup.auxRef(0)
    val wrB = cDup.auxRef(1)
    val cCons2 = cCons.copy()
    ptw.connectPrincipal(wrA, cCons)
    ptw.connectPrincipal(wrB, cCons2)
  }
}

final class Dup1RuleImpl(derivedMainSymId: Int) extends RuleImpl {
  def reduce(wr: WireRef, ptw: PerThreadWorker): Unit = {
    val c1 = wr.cell
    val c2 = wr.oppo.cell
    val (cDup, cCons) = if(c1.symId == derivedMainSymId) (c1, c2) else (c2, c1)
    val wrA = cDup.auxRef(0)
    val wrB = cDup.auxRef(1)
    val wrAux1 = cCons.auxRef(0)
    val cCons2 = cCons.copy()
    new WireRef(cCons, 0, cDup, 0)
    new WireRef(cCons2, 0, cDup, 1)
    ptw.connectPrincipal(wrA, cCons)
    ptw.connectPrincipal(wrB, cCons2)
    ptw.connectPrincipal(wrAux1, cDup)
  }
}

final class Dup2RuleImpl(derivedMainSymId: Int) extends RuleImpl {
  def reduce(wr: WireRef, ptw: PerThreadWorker): Unit = {
    val c1 = wr.cell
    val c2 = wr.oppo.cell
    val (cDup, cCons) = if(c1.symId == derivedMainSymId) (c1, c2) else (c2, c1)
    val wrA = cDup.auxRef(0)
    val wrB = cDup.auxRef(1)
    val wrAux1 = cCons.auxRef(0)
    val wrAux2 = cCons.auxRef(1)
    val cCons2 = cCons.copy()
    new WireRef(cCons, 0, cDup, 0)
    new WireRef(cCons2, 0, cDup, 1)
    val cDup2 = cDup.copy()
    new WireRef(cCons, 1, cDup2, 0)
    new WireRef(cCons2, 1, cDup2, 1)
    ptw.connectPrincipal(wrA, cCons)
    ptw.connectPrincipal(wrB, cCons2)
    ptw.connectPrincipal(wrAux1, cDup)
    ptw.connectPrincipal(wrAux2, cDup2)
  }
}

final class EraseRuleImpl(derivedMainSymId: Int) extends RuleImpl {
  def reduce(wr: WireRef, ptw: PerThreadWorker): Unit = {
    val c1 = wr.cell
    val c2 = wr.oppo.cell
    val (cErase, cCons) = if(c1.symId == derivedMainSymId) (c1, c2) else (c2, c1)
    val arity = cCons.arity
    var i = 0
    while(i < arity) {
      val wr = cCons.auxRef(i)
      ptw.connectPrincipal(wr, cErase.copy())
      i += 1
    }
  }
}

final class Interpreter(globals: Symbols, rules: Iterable[CheckedRule]) extends BaseInterpreter { self =>
  final val scope: Scope[Cell] = new Scope[Cell] {
    def createCell(sym: Symbol): Cell = if(sym.isCons) Cells.mk(getSymbolId(sym), sym.cons.arity) else new WireCell(sym, 0)
    def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit = new WireRef(c1, p1, c2, p2)
    def getSymbol(c: Cell): Symbol = c match {
      case c: WireCell => c.sym
      case c => reverseSymIds(c.symId)
    }
    def getConnected(c: Cell, port: Int): (Cell, Int) = Cells.getCell(c, port)
    def isFreeWire(c: Cell): Boolean = c.isInstanceOf[WireCell]
  }
  private[this] final val allSymbols = globals.symbols
  private[this] final val symIds = mutable.HashMap.from[Symbol, Int](allSymbols.zipWithIndex.map { case (s, i) => (s, i+1) })
  private[this] final val reverseSymIds = symIds.iterator.map { case (k, v) => (v, k) }.toMap
  private[this] final val symBits = Integer.numberOfTrailingZeros(Integer.highestOneBit(symIds.size))+1
  var totalSteps = 0

  def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)

  final val ruleImpls = new Array[RuleImpl](1 << (symBits << 1))
  private[this] final val maxRuleCells = createRuleImpls()

  def createTempCells(): Array[Cell] = new Array[Cell](maxRuleCells)

  def createRuleImpls(): Int = {
    val lookup = new SymbolIdLookup {
      override def getSymbolId(name: String): Int = self.getSymbolId(globals(new AST.Ident(name)))
    }
    val codeGen = new CodeGen[RuleImpl]("de/szeiger/interact/st2", "de/szeiger/interact/st2/gen")
    val ris = new ArrayBuffer[RuleImpl]()
    var max = 0
    rules.foreach { cr =>
      val s1 = globals(cr.name1)
      val s2 = globals(cr.name2)
      val rk = mkRuleKey(getSymbolId(s1), getSymbolId(s2))
      def generic = {
        val g = GenericRuleImpl(scope, cr.r.reduced, globals, s1, s2, cr.args1, cr.args2)
        //g.log()
        codeGen.compile(g)(lookup)
        //if(g.maxCells > max) max = g.maxCells
        //new InterpretedRuleImpl(s1id, g.cells.map(s => intOfShorts(getSymbolId(s), s.arity)), g.freeWiresPacked1, g.freWiresPacked2, g.connectionsPacked)
      }
      val ri = generic
//        if(cr.r.derived) {
//          (cr.name1.s, cr.args2.length) match {
//            case ("Dup", 0) => new Dup0RuleImpl(s1id)
//            case ("Dup", 1) => new Dup1RuleImpl(s1id)
//            case ("Dup", 2) => new Dup2RuleImpl(s1id)
//            case ("Erase", _) => new EraseRuleImpl(s1id)
//            case _ => generic
//          }
//        } else generic
      ruleImpls(rk) = ri
      ris.addOne(ri)
    }
    max
  }

  @inline def mkRuleKey(w: WireRef): Int =
    mkRuleKey(w.cell.symId, w.oppo.cell.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  def detectInitialCuts: CutBuffer = {
    val detected = mutable.HashSet.empty[WireRef]
    val buf = new CutBuffer(16)
    scope.reachableCells.foreach { c =>
      val w = c.pref
      val ri = ruleImpls(mkRuleKey(w))
      if(ri != null) {
        if(w.cellPort < 0 && w.oppo.cellPort < 0 && !detected.contains(w.oppo)) {
          detected.addOne(w)
          buf.addOne(w, ri)
        }
      }
    }
    buf
  }

  // Used by the debugger
  def getRuleImpl(wr: WireRef): RuleImpl = ruleImpls(mkRuleKey(wr))
  def reduce1(wr: WireRef): Unit = {
    val w = new PerThreadWorker(this) {
      protected[this] override def enqueueCut(wr: WireRef, ri: RuleImpl): Unit = ()
    }
    w.setNext(wr, getRuleImpl(wr))
    w.processNext()
  }

  def reduce(): Int = {
    totalSteps = 0
    val initial = detectInitialCuts
    val w = new PerThreadWorker(this) {
      protected[this] override def enqueueCut(wr: WireRef, ri: RuleImpl): Unit = initial.addOne(wr, ri)
    }
    while(initial.nonEmpty) {
      val (wr, ri) = initial.pop()
      w.setNext(wr, ri)
      w.processAll()
    }
    w.resetSteps
  }
}

final class CutBuffer(initialSize: Int) {
  private[this] var wrs = new Array[WireRef](initialSize)
  private[this] var ris = new Array[RuleImpl](initialSize)
  private[this] var len = 0
  @inline def addOne(wr: WireRef, ri: RuleImpl): Unit = {
    if(len == wrs.length) {
      wrs = Arrays.copyOf(wrs, wrs.length*2)
      ris = Arrays.copyOf(ris, ris.length*2)
    }
    wrs(len) = wr
    ris(len) = ri
    len += 1
  }
  @inline def nonEmpty: Boolean = len != 0
  @inline def pop(): (WireRef, RuleImpl) = {
    len -= 1
    val wr = wrs(len)
    val ri = ris(len)
    wrs(len) = null
    (wr, ri)
  }
}

abstract class PerThreadWorker(final val inter: Interpreter) {
  final val tempCells = inter.createTempCells()
  private[this] final var nextCut: WireRef = _
  private[this] final var nextRule: RuleImpl = _
  private[this] final var steps = 0

  final def resetSteps: Int = { val i = steps; steps = 0; i }

  protected[this] def enqueueCut(wr: WireRef, ri: RuleImpl): Unit

  final def connect(wr: WireRef, t: Cell, p: Int): Unit = {
    wr.cell = t; wr.cellPort = p
    if(p < 0) { t.pref = wr; if(wr.oppo.cellPort < 0) createCut(wr) }
    else t.setAuxRef(p, wr)
  }

  final def connectPrincipal(wr: WireRef, t: Cell): Unit = {
    wr.cell = t; wr.cellPort = -1; t.pref = wr
    if(wr.oppo.cellPort < 0) createCut(wr)
  }

  final def connectAux(wr: WireRef, t: Cell, a: Int): Unit = {
    wr.cell = t; wr.cellPort = a
    t.setAuxRef(a, wr)
  }

  // specialized for Cell arity + port
  final def connectAux_1_0(wr: WireRef, t: Cell1): Unit = { wr.cell = t; wr.cellPort = 0; t.aref0 = wr }
  final def connectAux_2_0(wr: WireRef, t: Cell2): Unit = { wr.cell = t; wr.cellPort = 0; t.aref0 = wr }
  final def connectAux_2_1(wr: WireRef, t: Cell2): Unit = { wr.cell = t; wr.cellPort = 1; t.aref1 = wr }

  final def connectFreeToFree(wr1: WireRef, wr2: WireRef): Unit = {
    val (wt, wp) = wr1.opposite
    connect(wr2, wt, wp)
  }

  final def createCut(wr: WireRef): Unit = {
    val ri = inter.ruleImpls(inter.mkRuleKey(wr))
    if(ri != null) {
      if(nextCut == null) { nextCut = wr; nextRule = ri }
      else enqueueCut(wr, ri)
    }
  }

  final def setNext(wr: WireRef, ri: RuleImpl): Unit = {
    this.nextCut = wr
    this.nextRule = ri
  }

  final def processNext(): Unit = {
    val c = nextCut
    val ri = nextRule
    nextCut = null
    ri.reduce(c, this)
  }

  @tailrec
  final def processAll(): Unit = {
    processNext()
    steps += 1
    if(nextCut != null) processAll()
  }
}
