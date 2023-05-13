package de.szeiger.interact.mt

import de.szeiger.interact.{AST, BaseInterpreter, CheckedRule, Symbol, Symbols}
import de.szeiger.interact.mt.workers.{Worker, Workers}

import java.io.PrintStream
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
  @inline def apply(): WireRef =
    new WireRef(null, 0, new AtomicInteger, null, null, 0)

  @inline def apply(c1: Cell, p1: Int, c2: Cell, p2: Int): WireRef =
    new WireRef(c1, p1, new AtomicInteger((if(p1 == 0) 1 else 0) + (if(p2 == 0) 1 else 0)), null, c2, p2)
}

final class WireRef(final var cell: Cell, final var cellPort: Int, private[this] final var _principals: AtomicInteger, _oppo: WireRef, _oppoCell: Cell, _oppoPort: Int) extends WireOrCell {
  if(cell != null) cell.setWire(cellPort, this)

  final var oppo: WireRef = if(_oppo != null) _oppo else new WireRef(_oppoCell, _oppoPort, _principals, this, null, 0)

  @inline private[this] def incLocked(pr0: AtomicInteger): Int = {
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
  @inline def connect(t: Cell, p: Int): Int = {
    t.setWire(p, this)
    cell = t;
    cellPort = p
    if(p == 0) incLocked(principals) else -1
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

abstract class Scope {
  val freeWires = mutable.HashSet.empty[WireCell]

  def getSymbolId(sym: Symbol): Int
  def getSymbolForId(symId: Int): Symbol
  def symbolName(c: Cell): String = {
    val sym = c match {
      case c: WireCell => c.sym
      case c => getSymbolForId(c.symId)
    }
    sym.id.s
  }

  private def addSymbols(cs: Iterable[AST.Cut], symbols: Symbols): Unit = {
    def f(e: AST.Expr): Unit = e match {
      case i: AST.Ident =>
        val s = symbols.getOrAdd(i)
        if(!s.isCons) s.refs += 1
      case AST.Ap(i, es) => f(i); es.foreach(f)
    }
    cs.foreach { c => f(c.left); f(c.right) }
  }

  def add(cuts: Iterable[AST.Cut], syms: Symbols): Unit = {
    def connectAny(t1: WireOrCell, p1: Int, t2: WireOrCell, p2: Int): Unit = {
      (t1, t2) match {
        case (t1: WireRef, t2: Cell) =>
          t1.connect(t2, p2)
        case (t1: Cell, t2: WireRef) =>
          t2.connect(t1, p1)
        case (t1: Cell, t2: Cell) =>
          Wire(t1, p1, t2, p2)
      }
    }
    addSymbols(cuts, syms)
    val bind = mutable.HashMap.empty[Symbol, WireRef]
    val toCreate = mutable.Queue.empty[(AST.Expr, Cell, Int)]
    def create(e: AST.Expr, cCell: Cell, cPort: Int): (WireOrCell, Int) = {
      val (wr, pr) = e match {
        case i: AST.Ident =>
          val s = syms.getOrAdd(i)
          if(s.isCons) {
            val s = syms.getOrAdd(i)
            val c = new Cell(getSymbolId(s), s.cons.arity)
            (c, 0)
          } else if(s.refs == 1) {
            val c = new WireCell(s, 0, 0)
            freeWires.addOne(c)
            (c, 0)
          } else if(s.refs == 2) {
            bind.get(s) match {
              case Some(w) => (w, 1)
              case None =>
                val w = Wire()
                bind.put(s, w.oppo)
                (w, 0)
            }
          } else sys.error(s"Non-linear use of ${i.show} in data")
        case AST.Ap(i, args) =>
          val s = syms.getOrAdd(i)
          assert(s.isCons)
          val c = new Cell(getSymbolId(s), s.cons.arity)
          args.zipWithIndex.foreach { case (a, idx) =>
            val p = idx + 1
            toCreate.enqueue((a, c, p))
          }
          (c, 0)
      }
      if(cCell != null) connectAny(cCell, cPort, wr, pr)
      (wr, pr)
    }
    def createCut(e: AST.Cut): Unit = {
      val (lt, ls) = create(e.left, null, 0)
      val (rt, rs) = create(e.right, null, 0)
      connectAny(lt, ls, rt, rs)
    }
    cuts.foreach { c =>
      createCut(c)
      while(!toCreate.isEmpty) {
        val (e, c, p) = toCreate.dequeue()
        create(e, c, p)
      }
    }
  }

  def validate(): Unit = {
    val wires =  reachableCells.flatMap(_.allPorts).toSet
    wires.foreach(w => w.cell == null || w.cell.getWireRef(w.cellPort) == w)
  }

  object Church {
    def unapply(_c: Cell): Option[Int] = {
      var acc = 0
      var c = _c
      while(true) {
        if(symbolName(c) == "Z" && c.arity == 0) return Some(acc)
        else if(symbolName(c) == "S" && c.arity == 1) {
          c.getCell(1) match {
            case (c2, 0) => c = c2; acc += 1
            case _ => return None
          }
        } else return None
      }
      return None
    }
  }

  object ListCons {
    def unapply(c: Cell): Option[(Cell, Cell)] = {
      if(symbolName(c) == "Cons" && c.arity == 2) {
        val (c1, p1) = c.getCell(1)
        val (c2, p2) = c.getCell(2)
        if(p1 == 0 && p2 == 0) Some((c1, c2)) else None
      } else None
    }
  }

  def reachableCells: Iterator[Cell] = {
    val s = mutable.HashSet.empty[Cell]
    val q = mutable.Queue.from(freeWires.flatMap(_.allCells.map(_._2._1)))
    while(!q.isEmpty) {
      val w = q.dequeue()
      if(s.add(w)) q.enqueueAll(w.allCells.map(_._2._1))
    }
    s.iterator
  }

  def getCutLogs(): Iterator[(WireRef, String, String, Option[String])] = {
    val freeWireNames = freeWires.map(symbolName)
    val leaders = mutable.HashMap.empty[WireRef, WireRef]
    def leader(w: WireRef): WireRef = leaders.getOrElse(w, leaders.getOrElseUpdate(w.oppo, w))
    val cuts = mutable.HashSet.from(reachableCells.filter(_.getCell(0)._2 == 0)).map { c =>
      val w1 = leader(c.pref)
      val w2 = leader(c.getCell(0)._1.pref)
      assert(w1 == w2)
      w1
    }
    var nextTemp = -1
    val helpers = mutable.Map.empty[WireRef, String]
    def explicit(w: WireRef): String = helpers.getOrElseUpdate(w, {
      nextTemp += 1
      "$" + nextTemp
    })
    def targetOrReplacement(w: WireRef, t: Cell, p: Int): String = helpers.get(w) match {
      case Some(s) => s
      case None if p == 0 => show(t)
      case None => explicit(w)
    }
    def show(c: Cell): String = c match {
      case Church(i) => s"$i'c"
      case c if c.symId == 0 => symbolName(c)
      case ListCons(c1, c2) => s"${show(c1)} :: ${show(c2)}"
      case c if c.arity == 0 => symbolName(c)
      case c => c.allCells.drop(1).map { case (wr, (t, p)) => targetOrReplacement(leader(wr), t, p) }.mkString(s"${symbolName(c)}(", ", ", ")")
    }
    val strs = cuts.iterator.map { w =>
      val l = leader(w)
      val c1 = l.cell
      val c2 = l.oppo.cell
      if(c1.symId == 0) (l, symbolName(c1), show(c2), None)
      else if(c2.symId == 0) (l, symbolName(c2), show(c1), None)
      else (l, explicit(w), show(c1), Some(show(c2)))
    }
    strs.zipWithIndex.toIndexedSeq.sortBy { case ((w, l, r, o), idx) =>
      val f = freeWireNames.contains(l)
      (!f, if(f) l else "", idx)
    }.iterator.map(_._1)
  }

  def log(out: PrintStream): Unit = {
    getCutLogs().foreach { case (w, l, r, o) =>
      out.println(s"  ${l} . ${r}")
      o.foreach(r2 => out.println(s"  ${l} . ${r2}"))
    }
  }
}

final class RuleImpl(final val protoCells: Array[Int],
  final val freeWiresPorts: Array[Int],
  final val connections: Array[Int]) {
  def log(): Unit = {
    println("  Proto cells:")
    protoCells.foreach(pc => println(s"  - $pc"))
    println("  Free wires:")
    freeWiresPorts.foreach { case IntOfShorts(w, p) => println(s"  - ($w, $p)") }
    println("  Connections:")
    connections.foreach { c => println(s"  - ${Seq(byte0(c), byte1(c), byte2(c), byte3(c)).mkString(",")}")}
  }
}

final class Interpreter(globals: Symbols, rules: Iterable[CheckedRule], numThreads: Int) extends Scope with BaseInterpreter { self =>
  private[this] final val allSymbols = globals.symbols
  private[this] final val symIds = mutable.HashMap.from[Symbol, Int](allSymbols.zipWithIndex.map { case (s, i) => (s, i+1) })
  private[this] final val reverseSymIds = symIds.iterator.map { case (k, v) => (v, k) }.toMap
  private[this] final val symBits = {
    val sz = symIds.size
    val high = Integer.highestOneBit(sz)
    if(sz == high) Integer.numberOfTrailingZeros(high) else Integer.numberOfTrailingZeros(high)+1
  }
  private[this] final val unfinished = new AtomicInteger(0)
  private[this] final var latch: CountDownLatch = _
  private[this] final val totalSteps = new AtomicInteger(0)

  def addTotalSteps(i: Int): Unit = totalSteps.addAndGet(i)
  def incUnfinished(): Unit = unfinished.incrementAndGet()
  def decUnfinished(i: Int): Unit = if(unfinished.addAndGet(-i) == 0) latch.countDown()
  def getUnfinished(): Int = unfinished.get()

  def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)
  def getSymbolForId(symId: Int): Symbol = reverseSymIds.getOrElse(symId, null)

  // This unused object makes mt branching workloads 20% faster. HotSpot optimization bug?
  private[this] final val boundaryRuleImpl = new RuleImpl(null, null, null)

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
      val ri = createRuleImpl(cr.r.reduced,
        if(s1id <= s2id) s1id else s2id, if(s1id <= s2id) s2id else s1id,
        if(s1id <= s2id) cr.args1 else cr.args2, if(s1id <= s2id) cr.args2 else cr.args1,
        globals)
      //ri.log()
      if(ri.protoCells.length > max) max = ri.protoCells.length
      ruleImpls(rk) = ri
      ris.addOne(ri)
    }
    max
  }

  def createRuleImpl(reduced: Seq[AST.Cut], symId1: Int, symId2: Int, args1: Seq[AST.Ident], args2: Seq[AST.Ident], globals: Symbols): RuleImpl = {
    //println(s"***** Preparing ${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}")
    val syms = new Symbols(Some(globals))
    val sc = new Scope {
      def getSymbolId(sym: Symbol): Int = self.getSymbolId(sym)
      def getSymbolForId(symId: Int): Symbol = self.getSymbolForId(symId)
    }
    sc.add(reduced, syms)
    sc.validate()
    //sc.log()
    val cells = sc.reachableCells.filter(_.symId != 0).toArray
    val freeLookup = sc.freeWires.iterator.map { w => (w.sym, w) }.toMap
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
    val freeWires = wires.map { w => lookup(w.getCell(0)._1) }
    val freePorts = wires.map(_.getCell(0)._2)
    val freeWiresPorts = freeWires.zip(freePorts).map { case (w, p) => checkedIntOfShorts(w, p) }
    new RuleImpl(protoCells, freeWiresPorts, conns.toArray)
  }

  @inline def mkRuleKey(w: WireRef): Int =
    mkRuleKey(w.cell.symId, w.oppo.cell.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  def detectInitialCuts: CutBuffer = {
    val detected = mutable.HashSet.empty[WireRef]
    val buf = new CutBuffer(16)
    reachableCells.foreach { c =>
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

  private[this] final def reduce(ri: RuleImpl, c1: Cell, c2: Cell, cells: Array[Cell]): Unit = {
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
      val w = Wire(t1, p1, t2, p2)
      if((p1 | p2) == 0) createCut(w)
      i += 1
    }

    @inline def cutTarget(i: Int) = if(i < c1.arity) c1.auxRef(i) else c2.auxRef(i-c1.arity)

    // Connect cut wire to new cell
    @inline
    def connectFreeToInternal(cIdx: Int, cp: Int, cutIdx: Int): Unit = {
      val wr = cutTarget(cutIdx)
      if(wr.connect(cells(cIdx), cp) == 2)
        createCut(wr)
    }

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
    def connectFreeToFree(cutIdx1: Int, cutIdx2: Int): Unit = {
      val wr1 = cutTarget(cutIdx1)
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
        if(wr2p.addAndGet(wr1pc + 20) == 2) createCut(wr1o)
      }
    }

    i = 0
    while(i < ri.freeWiresPorts.length) {
      val fwp = ri.freeWiresPorts(i)
      val fw = short0(fwp)
      if(fw >= 0) connectFreeToInternal(fw, short1(fwp), i)
      else if(i < -1-fw) connectFreeToFree(i, -1-fw)
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
    VarHandle.acquireFence()
    nextCut = null
    val (c1, c2) = if(c.cell.symId <= c.oppo.cell.symId) (c.cell, c.oppo.cell) else (c.oppo.cell, c.cell)
    reduce(ri, c1, c2, tempCells)
    VarHandle.releaseFence()
  }

  @tailrec
  final def processAll(): Unit = {
    processNext()
    steps += 1
    if(nextCut != null) processAll()
  }
}
