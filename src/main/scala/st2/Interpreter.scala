package de.szeiger.interact.st2

import de.szeiger.interact.{AST, BaseInterpreter, CheckedRule, Scope, Symbol, Symbols}
import de.szeiger.interact.mt.BitOps._

import java.util.Arrays
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.annotation.{switch, tailrec}

final class WireRef(final var cell: Cell, final var cellPort: Int, _oppo: WireRef, _oppoCell: Cell, _oppoPort: Int) {
  if(cell != null) cell.setWire(cellPort, this)

  final val oppo: WireRef = if(_oppo != null) _oppo else new WireRef(_oppoCell, _oppoPort, this, null, 0)

  def connect(t: Cell, p: Int): Boolean = {
    cell = t; cellPort = p
    if(p == 0) { t.pref = this; oppo.cellPort == 0 }
    else { t.setAuxRef(p-1, this); false }
  }
  @inline def opposite: (Cell, Int) = (oppo.cell, oppo.cellPort)
}

class Cell(final val symId: Int, final val arity: Int) {
  final var pref: WireRef = _
  private[this] final val auxRefs = new Array[WireRef](arity)
  def auxRef(i: Int): WireRef = auxRefs(i)
  def setAuxRef(i: Int, wr: WireRef): Unit = auxRefs(i) = wr
  @inline def setWire(slot: Int, w: WireRef) = {
    if(slot == 0) pref = w;
    else auxRefs(slot-1) = w
  }
  def getWireRef(slot: Int): WireRef =
    if(slot == 0) pref
    else auxRefs(slot-1)
  def getCell(p: Int): (Cell, Int) = {
    val w = getWireRef(p)
    if(w == null) null else w.opposite
  }
  def allPorts: Iterator[WireRef] = Iterator.single(pref) ++ auxRefs.iterator
  def allCells: Iterator[(WireRef, (Cell, Int))] = (0 to arity).iterator.map { i => (getWireRef(i), getCell(i)) }
  override def toString = s"Cell($symId, $arity, ${allPorts.map { case w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
  def copy() = new Cell(symId, arity)
}

class WireCell(final val sym: Symbol, _symId: Int, _arity: Int) extends Cell(_symId, _arity) {
  override def toString = s"WireCell($sym, $symId, $arity, ${allPorts.map { case w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
}

final class RuleImpl(final val protoCells: Array[Int],
  final val freeWiresPorts1: Array[Int], final val freeWiresPorts2: Array[Int],
  final val connections: Array[Int],
  final val ruleType: Int, final val derivedMainSymId: Int) {
  def log(): Unit = {
    println("  Proto cells:")
    protoCells.foreach(pc => println(s"  - $pc"))
    println("  Free wires:")
    freeWiresPorts1.foreach { case IntOfShorts(w, p) => println(s"  - ($w, $p)") }
    freeWiresPorts2.foreach { case IntOfShorts(w, p) => println(s"  - ($w, $p)") }
    println("  Connections:")
    connections.foreach { c => println(s"  - ${Seq(byte0(c), byte1(c), byte2(c), byte3(c)).mkString(",")}")}
  }
}

object RuleImpl {
  final val TYPE_DEFAULT = 0
  final val TYPE_DUP0    = 1
  final val TYPE_DUP1    = 2
  final val TYPE_DUP2    = 3
  final val TYPE_ERASE   = 4
}

final class Interpreter(globals: Symbols, rules: Iterable[CheckedRule]) extends BaseInterpreter { self =>
  final val scope: Scope[Cell] = new Scope[Cell] {
    def createCell(sym: Symbol): Cell = if(sym.isCons) new Cell(getSymbolId(sym), sym.cons.arity) else new WireCell(sym, 0, 0)
    def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit = new WireRef(c1, p1, null, c2, p2)
    def symbolName(c: Cell): String = c match {
      case c: WireCell => c.sym.id.s
      case c => reverseSymIds(c.symId).id.s
    }
    def getArity(c: Cell): Int = c.arity
    def getConnected(c: Cell, port: Int): (Cell, Int) = c.getCell(port)
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
    val ris = new ArrayBuffer[RuleImpl]()
    var max = 0
    rules.foreach { cr =>
      //println(s"***** Create rule ${cr.show}")
      val s1 = globals(cr.name1)
      val s2 = globals(cr.name2)
      val s1id = getSymbolId(s1)
      val s2id = getSymbolId(s2)
      val rk = mkRuleKey(s1id, s2id)
      val ruleType =
        if(cr.r.derived) {
          (cr.name1.s, cr.args2.length) match {
            case ("Dup", 0) => RuleImpl.TYPE_DUP0
            case ("Dup", 1) => RuleImpl.TYPE_DUP1
            case ("Dup", 2) => RuleImpl.TYPE_DUP2
            case ("Erase", _) => RuleImpl.TYPE_ERASE
            case _ => RuleImpl.TYPE_DEFAULT
          }
        } else RuleImpl.TYPE_DEFAULT
      val ri =
        if(ruleType == RuleImpl.TYPE_DEFAULT) {
          val ri = createRuleImpl(cr.r.reduced,
            if(s1id <= s2id) cr.args1 else cr.args2, if(s1id <= s2id) cr.args2 else cr.args1,
            globals, ruleType, s1id)
          if(ri.protoCells.length > max) max = ri.protoCells.length
          ri
        } else new RuleImpl(null, null, null, null, ruleType, s1id)
      ruleImpls(rk) = ri
      ris.addOne(ri)
    }
    max
  }

  def createRuleImpl(reduced: Seq[AST.Cut], args1: Seq[AST.Ident], args2: Seq[AST.Ident], globals: Symbols,
    ruleType: Int, derivedMainSymId: Int): RuleImpl = {
    //println(s"***** Preparing ${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}")
    val syms = new Symbols(Some(globals))
    val sc = new scope.Delegate
    sc.add(reduced, syms)
    sc.validate()
    //sc.log()
    val cells = sc.reachableCells.filter(_.symId != 0).toArray
    val freeLookup = sc.freeWires.iterator.map { w => (w.asInstanceOf[WireCell].sym, w) }.toMap
    val wires = (args1 ++ args2).map { i => freeLookup(syms(i)) }.toArray
    val lookup = (cells.iterator.zipWithIndex ++ wires.iterator.zipWithIndex.map { case (w, p) => (w, -p-1) }).toMap
    val protoCells = cells.map { c => intOfShorts(c.symId, c.arity) }
    val conns = mutable.HashSet.empty[Int]
    cells.iterator.zipWithIndex.foreach { case (c, i) =>
      c.allCells.zipWithIndex.foreach { case ((_, (t, p)), j) =>
        val w = lookup(t)
        if(w >= 0 && !conns.contains(checkedIntOfBytes(w, p, i, j)))
          conns.add(checkedIntOfBytes(i, j, w, p))
      }
    }
    val freeWiresPorts = wires.map { w => val (c, p) = w.getCell(0); checkedIntOfShorts(lookup(c), p) }
    val (fwp1, fwp2) = freeWiresPorts.splitAt(args1.length)
    new RuleImpl(protoCells, fwp1, fwp2, conns.toArray, ruleType, derivedMainSymId)
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
        if(w.cellPort == 0 && w.oppo.cellPort == 0 && !detected.contains(w.oppo)) {
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
  private[this] final val tempCells = inter.createTempCells()
  private[this] final var nextCut: WireRef = _
  private[this] final var nextRule: RuleImpl = _
  private[this] final var steps = 0

  final def resetSteps: Int = { val i = steps; steps = 0; i }

  protected[this] def enqueueCut(wr: WireRef, ri: RuleImpl): Unit

  @inline private[this] final def addCut(wr: WireRef, ri: RuleImpl): Unit = {
    if(nextCut == null) { nextCut = wr; nextRule = ri }
    else enqueueCut(wr, ri)
  }

  @inline private[this] final def createCut(t: WireRef): Unit = {
    val ri = inter.ruleImpls(inter.mkRuleKey(t))
    //println(s"createCut ${t.leftCell.sym} . ${t.rightCell.sym} = $ri")
    if(ri != null) addCut(t, ri)
  }

  private[this] final def reduceDup0(ri: RuleImpl, c1: Cell, c2: Cell): Unit = {
    val (cDup, cCons) = if(c1.symId == ri.derivedMainSymId) (c1, c2) else (c2, c1)
    val wrA = cDup.auxRef(0)
    val wrB = cDup.auxRef(1)
    if(wrA.connect(cCons, 0)) createCut(wrA)
    val cCons2 = cCons.copy()
    if(wrB.connect(cCons2, 0)) createCut(wrB)
  }

  private[this] final def reduceDup1(ri: RuleImpl, c1: Cell, c2: Cell): Unit = {
    val (cDup, cCons) = if(c1.symId == ri.derivedMainSymId) (c1, c2) else (c2, c1)
    val wrA = cDup.auxRef(0)
    val wrB = cDup.auxRef(1)
    val wrAux1 = cCons.auxRef(0)
    if(wrA.connect(cCons, 0)) createCut(wrA)
    val cCons2 = cCons.copy()
    if(wrB.connect(cCons2, 0)) createCut(wrB)
    if(wrAux1.connect(cDup, 0)) createCut(wrAux1)
    new WireRef(cCons, 1, null, cDup, 1)
    new WireRef(cCons2, 1, null, cDup, 2)
  }

  private[this] final def reduceDup2(ri: RuleImpl, c1: Cell, c2: Cell): Unit = {
    val (cDup, cCons) = if(c1.symId == ri.derivedMainSymId) (c1, c2) else (c2, c1)
    val wrA = cDup.auxRef(0)
    val wrB = cDup.auxRef(1)
    val wrAux1 = cCons.auxRef(0)
    val wrAux2 = cCons.auxRef(1)
    if(wrA.connect(cCons, 0)) createCut(wrA)
    val cCons2 = cCons.copy()
    if(wrB.connect(cCons2, 0)) createCut(wrB)

    if(wrAux1.connect(cDup, 0)) createCut(wrAux1)
    new WireRef(cCons, 1, null, cDup, 1)
    new WireRef(cCons2, 1, null, cDup, 2)

    val cDup2 = cDup.copy()
    if(wrAux2.connect(cDup2, 0)) createCut(wrAux2)
    new WireRef(cCons, 2, null, cDup2, 1)
    new WireRef(cCons2, 2, null, cDup2, 2)
  }

  private[this] final def reduceErase(ri: RuleImpl, c1: Cell, c2: Cell): Unit = {
    val (cErase, cCons) = if(c1.symId == ri.derivedMainSymId) (c1, c2) else (c2, c1)
    val arity = cCons.arity
    var i = 0
    while(i < arity) {
      val wr = cCons.auxRef(i)
      if(wr.connect(cErase.copy(), 0)) createCut(wr)
      i += 1
    }
  }

  private[this] def delay(nanos: Int): Unit = {
    val end = System.nanoTime() + nanos
    while(System.nanoTime() < end) Thread.onSpinWait()
  }

  private[this] final def reduce(ri: RuleImpl, c1: Cell, c2: Cell, cells: Array[Cell]): Unit = {
    //delay(20)
    var i = 0
    while(i < ri.protoCells.length) {
      val pc = ri.protoCells(i)
      val sid = short0(pc)
      val ari = short1(pc)
      cells(i) = new Cell(sid, ari)
      i += 1
    }
    i = 0
    while(i < ri.connections.length) {
      val conn = ri.connections(i)
      val t1 = cells(byte0(conn))
      val p1 = byte1(conn)
      val t2 = cells(byte2(conn))
      val p2 = byte3(conn)
      val w = new WireRef(t1, p1, null, t2, p2)
      if((p1 | p2) == 0) createCut(w)
      i += 1
    }

    @inline def cutTarget(i: Int) = if(i < c1.arity) c1.auxRef(i) else c2.auxRef(i-c1.arity)

    // Connect cut wire to new cell
    @inline
    def connectFreeToInternal(cIdx: Int, cp: Int, wr: WireRef): Unit = {
      if(wr.connect(cells(cIdx), cp))
        createCut(wr)
    }

    // Connect 2 cut wires
    @inline
    def connectFreeToFree(wr1: WireRef, cutIdx2: Int): Unit = {
      val wr2 = cutTarget(cutIdx2)
      val (wt, wp) = wr1.opposite
      if(wr2.connect(wt, wp)) createCut(wr2)
    }

    i = 0
    while(i < ri.freeWiresPorts1.length) {
      val fwp = ri.freeWiresPorts1(i)
      val fw = short0(fwp)
      if(fw >= 0) connectFreeToInternal(fw, short1(fwp), c1.auxRef(i))
      else if(i < -1-fw) connectFreeToFree(c1.auxRef(i), -1-fw)
      i += 1
    }
    i = 0
    while(i < ri.freeWiresPorts2.length) {
      val fwp = ri.freeWiresPorts2(i)
      val fw = short0(fwp)
      if(fw >= 0) connectFreeToInternal(fw, short1(fwp), c2.auxRef(i))
      else if(i+c1.arity < -1-fw) connectFreeToFree(c2.auxRef(i), -1-fw)
      i += 1
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
    (ri.ruleType: @switch) match {
      case RuleImpl.TYPE_DUP0 => reduceDup0(ri, c.cell, c.oppo.cell)
      case RuleImpl.TYPE_DUP1 => reduceDup1(ri, c.cell, c.oppo.cell)
      case RuleImpl.TYPE_DUP2 => reduceDup2(ri, c.cell, c.oppo.cell)
      case RuleImpl.TYPE_ERASE => reduceErase(ri, c.cell, c.oppo.cell)
      case RuleImpl.TYPE_DEFAULT =>
        val (c1, c2) = if(c.cell.symId <= c.oppo.cell.symId) (c.cell, c.oppo.cell) else (c.oppo.cell, c.cell)
        reduce(ri, c1, c2, tempCells)
    }
  }

  @tailrec
  final def processAll(): Unit = {
    processNext()
    steps += 1
    if(nextCut != null) processAll()
  }
}
