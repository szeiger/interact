package de.szeiger.interact.mt

import de.szeiger.interact.{AST, BaseInterpreter, CheckedRule, Scope, Symbol, Symbols}
import de.szeiger.interact.mt.workers.{Worker, Workers}

import java.util.Arrays
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import BitOps._

import java.lang.invoke.{MethodHandles, VarHandle}
import java.util.concurrent.{CountDownLatch, ForkJoinPool, ForkJoinWorkerThread, RecursiveAction, TimeUnit}
import scala.annotation.tailrec

sealed trait WireOrCell

object Wire {
  @inline def apply(c1: Cell, p1: Int, c2: Cell, p2: Int): WireRef =
    new WireRef(c1, p1, new AtomicInteger((if(p1 < 0) 1 else 0) + (if(p2 < 0) 1 else 0)), null, c2, p2)
}

final class WireRef(final var cell: Cell, final var cellPort: Int, private[this] final var _principals: AtomicInteger, _oppo: WireRef, _oppoCell: Cell, _oppoPort: Int) extends WireOrCell {
  if(cell != null) cell.setWire(cellPort, this)

  final var oppo: WireRef = if(_oppo != null) _oppo else new WireRef(_oppoCell, _oppoPort, _principals, this, null, 0)

  @inline def incLocked(): Int = {
    val pr0 = principals
    var pr1 = pr0
    val v = pr1.incrementAndGet()
    if(v >= -10) return v
    while(pr1 eq pr0) {
      Thread.onSpinWait()
      pr1 = principals
    }
    pr1.incrementAndGet()
  }
  @inline def principals: AtomicInteger = WireRef.PRINCIPALS.getOpaque(this).asInstanceOf[AtomicInteger]
  @inline def principals_= (p: AtomicInteger): Unit = WireRef.PRINCIPALS.setOpaque(this,p)
  def connectOnly(t: Cell, p: Int): Boolean = {
    t.setWire(p, this)
    cell = t;
    cellPort = p
    if(p == 0) incLocked() == 2 else false
  }
  @inline def opposite: (Cell, Int) = (oppo.cell, oppo.cellPort)
  @inline def getPrincipals = principals.get
  @inline def tryLock: Boolean = {
    val p = getPrincipals
    p >= 0 && principals.weakCompareAndSetVolatile(p, p-10)
  }
  @tailrec @inline def lock: Unit = if(!tryLock) { Thread.onSpinWait(); lock }
  @inline def unlock: Unit = principals.addAndGet(10)
}

object WireRef {
  final val PRINCIPALS =
    MethodHandles.privateLookupIn(classOf[WireRef], MethodHandles.lookup).findVarHandle(classOf[WireRef], "_principals", classOf[AtomicInteger])
}

class Cell(final val symId: Int, final val arity: Int) extends WireOrCell {
  final var pref: WireRef = _
  private[this] final val auxRefs = new Array[WireRef](arity)
  def auxRef(p: Int): WireRef = auxRefs(p)
  def setAuxRef(p: Int, wr: WireRef): Unit = auxRefs(p) = wr
  @inline def setWire(p: Int, w: WireRef) =
    if(p < 0) pref = w else auxRefs(p) = w
  def getWireRef(p: Int): WireRef =
    if(p < 0) pref else auxRefs(p)
  def getCell(p: Int): (Cell, Int) = {
    val w = getWireRef(p)
    if(w == null) null else w.opposite
  }
  def allPorts: Iterator[WireRef] = Iterator.single(pref) ++ auxRefs.iterator
  def allCells: Iterator[(WireRef, (Cell, Int))] = (-1 until arity).iterator.map { i => (getWireRef(i), getCell(i)) }
  override def toString = s"Cell($symId, $arity, ${allPorts.map { case w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
  def copy() = new Cell(symId, arity)
}

class WireCell(final val sym: Symbol, _symId: Int, _arity: Int) extends Cell(_symId, _arity) {
  override def toString = s"WireCell($sym, $symId, $arity, ${allPorts.map { case w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
}

abstract class RuleImpl {
  def reduce(wr: WireRef, ptw: PerThreadWorker): Unit
}

final class GenericRuleImpl(protoCells: Array[Int], freeWiresPorts1: Array[Int], freeWiresPorts2: Array[Int], connections: Array[Int]) extends RuleImpl {
  def maxCells: Int = protoCells.length
  def maxWires = connections.length + freeWiresPorts1.length + freeWiresPorts2.length

  def log(): Unit = {
    println("  Proto cells:")
    protoCells.foreach(pc => println(s"  - $pc"))
    println("  Free wires:")
    freeWiresPorts1.foreach { case IntOfShorts(w, p) => println(s"  - ($w, $p)") }
    freeWiresPorts2.foreach { case IntOfShorts(w, p) => println(s"  - ($w, $p)") }
    println("  Connections:")
    connections.foreach { c => println(s"  - ${Seq(byte0(c), byte1(c), byte2(c), byte3(c)).mkString(",")}")}
  }

  private[this] def delay(nanos: Int): Unit = {
    val end = System.nanoTime() + nanos
    while(System.nanoTime() < end) Thread.onSpinWait()
  }

  def reduce(wr: WireRef, ptw: PerThreadWorker): Unit = {
    val (c1, c2) = if(wr.cell.symId <= wr.oppo.cell.symId) (wr.cell, wr.oppo.cell) else (wr.oppo.cell, wr.cell)
    val cells = ptw.tempCells
    //delay(20)
    var i = 0
    while(i < protoCells.length) {
      val pc = protoCells(i)
      val sid = short0(pc)
      val ari = short1(pc)
      cells(i) = new Cell(sid, ari)
      i += 1
    }

    @inline def cutTarget(i: Int) = if(i < c1.arity) c1.auxRef(i) else c2.auxRef(i-c1.arity)

    // Connect cut wire to new cell
    @inline def connectFreeToInternal(cIdx: Int, cp: Int, wr: WireRef): Unit =
      ptw.connectDeferred(wr, cells(cIdx), cp)

    @tailrec @inline
    def lock2(wr1: WireRef, wr2: WireRef): Boolean = {
      wr1.lock
      if(wr1.oppo eq wr2) false
      else if(wr2.tryLock) true
      else {
        wr1.unlock
        Thread.onSpinWait()
        lock2(wr2, wr1)
      }
    }

    // Connect 2 cut wires
    @inline
    def connectFreeToFree(wr1: WireRef, cutIdx2: Int): Unit = {
      val wr2 = cutTarget(cutIdx2)
      /*if(wr1.getPrincipals == 1) { // take ownership of opposing cell on t
        val (wt, wp) = wr1.opposite
        if(connectInc(wt, wp, wr2) == 2) createCut(wr2)
      } else if(wr2.getPrincipals == 1) { // take ownership of opposing cell on t2
        val (wt, wp) = wr2.opposite
        if(connectInc(wt, wp, wr1) == 2) createCut(wr1)
      } else*/ if(lock2(wr1, wr2)) { // ownership unclear -> lock and join wires
        val wr1o = wr1.oppo
        val wr2o = wr2.oppo
        val wr1p = wr1.principals
        val wr2p = wr2.principals
        wr1o.oppo = wr2o
        wr2o.oppo = wr1o
        val wr1pc = wr1p.getAndAdd(-100)
        wr1o.principals = wr2p
        if(wr2p.addAndGet(wr1pc + 20) == 2) ptw.createCut(wr1o)
      }
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

    i = 0
    while(i < connections.length) {
      val conn = connections(i)
      val t1 = cells(byte0(conn))
      val p1 = byte1(conn)
      val t2 = cells(byte2(conn))
      val p2 = byte3(conn)
      val w = Wire(t1, p1, t2, p2)
      if(p1 < 0 && p2 < 0) ptw.createCut(w)
      i += 1
    }

    ptw.flushDeferred()
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
    Wire(cCons, 0, cDup, 0)
    Wire(cCons2, 0, cDup, 1)
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
    val cDup2 = cDup.copy()
    Wire(cCons, 0, cDup, 0)
    Wire(cCons2, 0, cDup, 1)
    Wire(cCons, 1, cDup2, 0)
    Wire(cCons2, 1, cDup2, 1)
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


final class Interpreter(globals: Symbols, rules: Iterable[CheckedRule], numThreads: Int) extends BaseInterpreter { self =>
  final val scope: Scope[Cell] = new Scope[Cell] {
    def createCell(sym: Symbol): Cell = if(sym.isCons) new Cell(getSymbolId(sym), sym.cons.arity) else new WireCell(sym, 0, 0)
    def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit = Wire(c1, p1, c2, p2)
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
  private[this] final val unfinished = new AtomicInteger(0)
  private[this] final var latch: CountDownLatch = _
  private[this] final val totalSteps = new AtomicInteger(0)

  def addTotalSteps(i: Int): Unit = totalSteps.addAndGet(i)
  def incUnfinished(): Unit = unfinished.incrementAndGet()
  def decUnfinished(i: Int): Unit = if(unfinished.addAndGet(-i) == 0) latch.countDown()
  def getUnfinished(): Int = unfinished.get()

  def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)

  // This unused object makes mt branching workloads 20% faster. HotSpot optimization bug?
  private[this] final val boundaryRuleImpl = new GenericRuleImpl(null, null, null, null)

  final val ruleImpls = new Array[RuleImpl](1 << (symBits << 1))
  private[this] final val (maxRuleCells, maxRuleWires) = createRuleImpls()

  def createTempCells(): Array[Cell] = new Array[Cell](maxRuleCells)
  def createTempWires(): Array[WireRef] = new Array[WireRef](maxRuleWires)

  def createRuleImpls(): (Int, Int) = {
    val ris = new ArrayBuffer[RuleImpl]()
    var maxC, maxW = 0
    rules.foreach { cr =>
      //println(s"***** Create rule ${cr.show}")
      val s1 = globals(cr.name1)
      val s2 = globals(cr.name2)
      val s1id = getSymbolId(s1)
      val s2id = getSymbolId(s2)
      val rk = mkRuleKey(s1id, s2id)
      def generic = {
        val ri = createRuleImpl(cr.r.reduced, globals,
          if(s1id <= s2id) cr.args1 else cr.args2, if(s1id <= s2id) cr.args2 else cr.args1)
        if(ri.maxCells > maxC) maxC = ri.maxCells
        if(ri.maxWires > maxW) maxW = ri.maxWires
        ri
      }
      val ri =
        if(cr.r.derived) {
          (cr.name1.s, cr.args2.length) match {
            case ("Dup", 0) => new Dup0RuleImpl(s1id)
            case ("Dup", 1) => new Dup1RuleImpl(s1id)
            case ("Dup", 2) => new Dup2RuleImpl(s1id)
            case ("Erase", _) => new EraseRuleImpl(s1id)
            case _ => generic
          }
        } else generic
      ruleImpls(rk) = ri
      ris.addOne(ri)
    }
    (maxC, maxW)
  }

  def createRuleImpl(reduced: Seq[AST.Cut], globals: Symbols, args1: Seq[AST.Ident], args2: Seq[AST.Ident]): GenericRuleImpl = {
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
        if(w >= 0 && !conns.contains(checkedIntOfBytes(w, p, i, j-1)))
          conns.add(checkedIntOfBytes(i, j-1, w, p))
      }
    }
    // Make principal connections last to ensure auxiliary wires are already connected and get published
    val (connsPrinc, connsAux) = conns.toArray.partition(i => (byte1(i) | byte3(i)) == 0)
    val orderedConns = connsAux ++ connsPrinc
    val freeWiresPorts = wires.map { w => val (c, p) = w.getCell(-1); checkedIntOfShorts(lookup(c), p) }
    val (fwp1, fwp2) = freeWiresPorts.splitAt(args1.length)
    new GenericRuleImpl(protoCells, fwp1, fwp2, orderedConns)
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
    totalSteps.set(0)
    val initial = detectInitialCuts
    if(numThreads == 0) {
      val w = new PerThreadWorker(this) {
        protected[this] override def enqueueCut(wr: WireRef, ri: RuleImpl): Unit = initial.addOne(wr, ri)
      }
      while(initial.nonEmpty) {
        val (wr, ri) = initial.pop()
        w.setNext(wr, ri)
        w.processAll()
      }
      w.resetSteps
    } else if(numThreads <= 1000) {
      latch = new CountDownLatch(1)
      val pool = new ForkJoinPool(numThreads, new ActionWorkerThread(_, this), null, numThreads > 1)
      unfinished.addAndGet(initial.length)
      initial.foreach { (wr, ri) => pool.execute(new Action(wr, ri)) }
      while(unfinished.get() != 0) latch.await()
      pool.shutdown()
      totalSteps.get()
    } else {
      latch = new CountDownLatch(1)
      class Adapter extends Worker[(WireRef, RuleImpl)] {
        var dec = 0
        val worker = new PerThreadWorker(self) {
          protected[this] def enqueueCut(wr: WireRef, ri: RuleImpl): Unit = {
            inter.incUnfinished()
            add((wr, ri))
          }
        }
        override def apply(t: (WireRef, RuleImpl)): Unit = {
          worker.setNext(t._1, t._2)
          worker.processAll()
          worker.inter.addTotalSteps(worker.resetSteps)
          dec += 1
        }
        override def maybeEmpty(): Unit = {
          //println(s"done: $dec, unfinished: ${worker.inter.getUnfinished()}")
          worker.inter.decUnfinished(dec)
          dec = 0
        }
      }
      val workers = new Workers[(WireRef, RuleImpl)](numThreads-1000, 8, _ => new Adapter)
      unfinished.addAndGet(initial.length)
      workers.start()
      initial.foreach { (wr, ri) => workers.add((wr, ri)) }
      while(unfinished.get() != 0) latch.await()
      workers.shutdown()
      totalSteps.get()
    }
  }
}

final class Action(startCut: WireRef, startRule: RuleImpl) extends RecursiveAction {
  def compute(): Unit = {
    val w = Thread.currentThread().asInstanceOf[ActionWorkerThread].worker
    w.setNext(startCut, startRule)
    w.processAll()
    w.inter.addTotalSteps(w.resetSteps)
    w.inter.decUnfinished(1)
  }
}

final class ActionWorkerThread(pool: ForkJoinPool, _inter: Interpreter) extends ForkJoinWorkerThread(pool) {
  final val worker: PerThreadWorker = new PerThreadWorker(_inter) {
    protected[this] def enqueueCut(wr: WireRef, ri: RuleImpl): Unit = {
      inter.incUnfinished()
      new Action(wr, ri).fork()
    }
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
  @inline def length: Int = len
  @inline def foreach(f: (WireRef, RuleImpl) => Unit): Unit = {
    var i = 0
    while(i < len) {
      f(wrs(i), ris(i))
      i += 1
    }
  }
}

abstract class PerThreadWorker(final val inter: Interpreter) {
  final val tempCells = inter.createTempCells()
  private[this] final val tempWires = inter.createTempWires()
  private[this] final var usedTempWires = 0
  private[this] final var nextCut: WireRef = _
  private[this] final var nextRule: RuleImpl = _
  private[this] final var steps = 0

  final def resetSteps: Int = { val i = steps; steps = 0; i }

  protected[this] def enqueueCut(wr: WireRef, ri: RuleImpl): Unit

  def connect(wr: WireRef, t: Cell, p: Int): Unit = {
    wr.cell = t; wr.cellPort = p
    if(p < 0) { t.pref = wr; if(wr.incLocked() == 2) createCut(wr) }
    else t.setAuxRef(p, wr)
  }

  def connectPrincipal(wr: WireRef, t: Cell): Unit = {
    wr.cell = t; wr.cellPort = -1; t.pref = wr
    if(wr.incLocked() == 2) createCut(wr)
  }

  def connectAux(wr: WireRef, t: Cell, p: Int): Unit = {
    wr.cell = t; wr.cellPort = p
    t.setAuxRef(p, wr)
  }

  def connectDeferred(wr: WireRef, t: Cell, p: Int): Unit = {
    wr.cell = t; wr.cellPort = p
    if(p < 0) { t.pref = wr; tempWires(usedTempWires) = wr; usedTempWires += 1 }
    else t.setAuxRef(p, wr)
  }

  def flushDeferred(): Unit = {
    var i = 0
    while(i < usedTempWires) {
      val wr = tempWires(i)
      tempWires(i) = null
      if(wr.incLocked() == 2) createCut(wr)
      i += 1
    }
    usedTempWires = 0
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
    VarHandle.acquireFence()
    nextCut = null
    ri.reduce(c, this)
    VarHandle.releaseFence()
  }

  @tailrec
  final def processAll(): Unit = {
    processNext()
    steps += 1
    if(nextCut != null) processAll()
  }
}
