package de.szeiger.interact.st2

import de.szeiger.interact.{AST, BaseInterpreter, CheckedRule, Symbol, Symbols}
import de.szeiger.interact.mt.BitOps._

import java.io.PrintStream
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.annotation.{switch, tailrec}

sealed trait WireOrCell

final class WireRef(final var cell: Cell, final var cellPort: Int, _oppo: WireRef, _oppoCell: Cell, _oppoPort: Int) extends WireOrCell {
  if(cell != null) cell.setWire(cellPort, this)

  final val oppo: WireRef = if(_oppo != null) _oppo else new WireRef(_oppoCell, _oppoPort, this, null, 0)

  @inline def connect(t: Cell, p: Int): Boolean = {
    t.setWire(p, this)
    cell = t;
    cellPort = p
    p == 0 && oppo.cellPort == 0
  }
  @inline def opposite: (Cell, Int) = (oppo.cell, oppo.cellPort)
}

final class Cell(final val sym: Symbol, final val symId: Int, final val arity: Int) extends WireOrCell {
  final var pref: WireRef = _
  final val auxRefs = new Array[WireRef](arity)
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
  override def toString = s"Cell($sym, $symId, $arity, ${allPorts.map { case w => s"(${if(w == null) "null" else "_"})" }.mkString(", ") })"
}

class Scope {
  val freeWires = mutable.HashSet.empty[Cell]

  def getSymbolId(sym: Symbol): Int = 0

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
          new WireRef(t1, p1, null, t2, p2)
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
            val c = new Cell(s, getSymbolId(s), s.cons.arity)
            (c, 0)
          } else if(s.refs == 1) {
            val c = new Cell(s, 0, 0)
            freeWires.addOne(c)
            (c, 0)
          } else if(s.refs == 2) {
            bind.get(s) match {
              case Some(w) => (w, 1)
              case None =>
                val w = new WireRef(null, 0, null, null, 0)
                bind.put(s, w.oppo)
                (w, 0)
            }
          } else sys.error(s"Non-linear use of ${i.show} in data")
        case AST.Ap(i, args) =>
          val s = syms.getOrAdd(i)
          assert(s.isCons)
          val c = new Cell(s, getSymbolId(s), s.cons.arity)
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
        if(c.sym.id.s == "Z" && c.arity == 0) return Some(acc)
        else if(c.sym.id.s == "S" && c.arity == 1) {
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
      if(c.sym.id.s == "Cons" && c.arity == 2) {
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
    val freeWireNames = freeWires.map(_.sym.toString)
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
      case c if c.symId == 0 => c.sym.toString
      case ListCons(c1, c2) => s"${show(c1)} :: ${show(c2)}"
      case c if c.arity == 0 => c.sym.toString
      case c => c.allCells.drop(1).map { case (wr, (t, p)) => targetOrReplacement(leader(wr), t, p) }.mkString(s"${c.sym}(", ", ", ")")
    }
    val strs = cuts.iterator.map { w =>
      val l = leader(w)
      val c1 = l.cell
      val c2 = l.oppo.cell
      if(c1.symId == 0) (l, c1.sym.toString, show(c2), None)
      else if(c2.symId == 0) (l, c2.sym.toString, show(c1), None)
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

final class ProtoCell(final val sym: Symbol, final val symId: Int, final val arity: Int) {
  def createCell = new Cell(sym, symId, arity)
  override def toString = s"ProtoCell($sym, $symId, $arity)"
}

final class RuleImpl(cr: CheckedRule, final val protoCells: Array[ProtoCell],
  final val freeWires: Array[Int], final val freePorts: Array[Int],
  final val connections: Array[Int], final val ruleImpls: Array[RuleImpl],
  final val ruleType: Int, final val derivedMainSymId: Int) {
  def symIdForCell(idx: Int) = protoCells(idx).symId
  def log(): Unit = {
    println("  Proto cells:")
    protoCells.foreach(pc => println(s"  - $pc"))
    println("  Free wires:")
    freeWires.zip(freePorts).foreach { case (w, p) => println(s"  - ($w, $p)") }
    println("  Connections:")
    connections.zip(ruleImpls).foreach { case (c, ri) => println(s"  - ${Seq(byte0(c), byte1(c), byte2(c), byte3(c)).mkString(",")}: $ri")}
  }
  override def toString = cr.show
}

object RuleImpl {
  final val TYPE_DEFAULT = 0
  final val TYPE_DUP0    = 1
  final val TYPE_DUP1    = 2
  final val TYPE_DUP2    = 3
  final val TYPE_ERASE   = 4
}

final class Interpreter(globals: Symbols, rules: Iterable[CheckedRule]) extends Scope with BaseInterpreter { self =>
  private[this] final val allSymbols = globals.symbols
  private[this] final val symIds = mutable.HashMap.from[Symbol, Int](allSymbols.zipWithIndex.map { case (s, i) => (s, i+1) })
  private[this] final val symBits = {
    val sz = symIds.size
    val high = Integer.highestOneBit(sz)
    if(sz == high) Integer.numberOfTrailingZeros(high) else Integer.numberOfTrailingZeros(high)+1
  }
  var totalSteps = 0

  override def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)

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
          val ri = createRuleImpl(cr, cr.r.reduced,
            if(s1id <= s2id) cr.args1 else cr.args2, if(s1id <= s2id) cr.args2 else cr.args1,
            globals, ruleType, s1id)
          if(ri.protoCells.length > max) max = ri.protoCells.length
          ri
        } else new RuleImpl(cr, null, null, null, null, null, ruleType, s1id)
      ruleImpls(rk) = ri
      ris.addOne(ri)
    }
    ris.foreach { ri =>
      if(ri.connections != null)
        ri.connections.zipWithIndex.foreach { case (IntOfBytes(t1, p1, t2, p2), i) =>
          if(p1 == 0 && p2 == 0)
            ri.ruleImpls(i) = ruleImpls(mkRuleKey(ri.symIdForCell(t1), ri.symIdForCell(t2)))
        }
    }
    max
  }

  def createRuleImpl(cr: CheckedRule, reduced: Seq[AST.Cut], args1: Seq[AST.Ident], args2: Seq[AST.Ident], globals: Symbols,
    ruleType: Int, derivedMainSymId: Int): RuleImpl = {
    //println(s"***** Preparing ${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}")
    val syms = new Symbols(Some(globals))
    val sc = new Scope { override def getSymbolId(sym: Symbol): Int = self.getSymbolId(sym) }
    sc.add(reduced, syms)
    sc.validate()
    //sc.log()
    val cells = sc.reachableCells.filter(_.symId != 0).toArray
    val freeLookup = sc.freeWires.iterator.map { w => (w.sym, w) }.toMap
    val wires = (args1 ++ args2).map { i => freeLookup(syms(i)) }.toArray
    val lookup = (cells.iterator.zipWithIndex ++ wires.iterator.zipWithIndex.map { case (w, p) => (w, -p-1) }).toMap
    val protoCells = cells.map { c => new ProtoCell(c.sym, getSymbolId(c.sym), c.arity) }
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
    new RuleImpl(cr, protoCells, freeWires, freePorts, conns.toArray, new Array(conns.size), ruleType, derivedMainSymId)
  }

  @inline def mkRuleKey(w: WireRef): Int =
    mkRuleKey(w.cell.symId, w.oppo.cell.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  def detectInitialCuts: ArrayBuffer[(WireRef, RuleImpl)] = {
    val detected = mutable.HashSet.empty[WireRef]
    val buf = ArrayBuffer.empty[(WireRef, RuleImpl)]
    reachableCells.foreach { c =>
      val w = c.pref
      val ri = ruleImpls(mkRuleKey(w))
      if(ri != null) {
        if(w.cellPort == 0 && w.oppo.cellPort == 0 && !detected.contains(w.oppo)) {
          detected.addOne(w)
          buf.addOne((w, ri))
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
      protected[this] override def enqueueCut(wr: WireRef, ri: RuleImpl): Unit = initial.addOne((wr, ri))
    }
    while(initial.nonEmpty) {
      val (wr, ri) = initial.last
      initial.dropRightInPlace(1)
      w.setNext(wr, ri)
      w.processAll()
    }
    w.resetSteps
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
    val wrA = cDup.auxRefs(0)
    val wrB = cDup.auxRefs(1)
    if(wrA.connect(cCons, 0)) createCut(wrA)
    val cCons2 = new Cell(cCons.sym, cCons.symId, cCons.arity)
    if(wrB.connect(cCons2, 0)) createCut(wrB)
  }

  private[this] final def reduceDup1(ri: RuleImpl, c1: Cell, c2: Cell): Unit = {
    val (cDup, cCons) = if(c1.symId == ri.derivedMainSymId) (c1, c2) else (c2, c1)
    val wrA = cDup.auxRefs(0)
    val wrB = cDup.auxRefs(1)
    val wrAux1 = cCons.auxRefs(0)
    if(wrA.connect(cCons, 0)) createCut(wrA)
    val cCons2 = new Cell(cCons.sym, cCons.symId, cCons.arity)
    if(wrB.connect(cCons2, 0)) createCut(wrB)
    if(wrAux1.connect(cDup, 0)) createCut(wrAux1)
    new WireRef(cCons, 1, null, cDup, 1)
    new WireRef(cCons2, 1, null, cDup, 2)
  }

  private[this] final def reduceDup2(ri: RuleImpl, c1: Cell, c2: Cell): Unit = {
    val (cDup, cCons) = if(c1.symId == ri.derivedMainSymId) (c1, c2) else (c2, c1)
    val wrA = cDup.auxRefs(0)
    val wrB = cDup.auxRefs(1)
    val wrAux1 = cCons.auxRefs(0)
    val wrAux2 = cCons.auxRefs(1)
    if(wrA.connect(cCons, 0)) createCut(wrA)
    val cCons2 = new Cell(cCons.sym, cCons.symId, cCons.arity)
    if(wrB.connect(cCons2, 0)) createCut(wrB)

    if(wrAux1.connect(cDup, 0)) createCut(wrAux1)
    new WireRef(cCons, 1, null, cDup, 1)
    new WireRef(cCons2, 1, null, cDup, 2)

    val cDup2 = new Cell(cDup.sym, cDup.symId, 2)
    if(wrAux2.connect(cDup2, 0)) createCut(wrAux2)
    new WireRef(cCons, 2, null, cDup2, 1)
    new WireRef(cCons2, 2, null, cDup2, 2)
  }

  private[this] final def reduceErase(ri: RuleImpl, c1: Cell, c2: Cell): Unit = {
    val (cErase, cCons) = if(c1.symId == ri.derivedMainSymId) (c1, c2) else (c2, c1)
    val arity = cCons.arity
    var i = 0
    while(i < arity) {
      val wr = cCons.auxRefs(i)
      if(wr.connect(new Cell(cErase.sym, cErase.symId, 0), 0)) createCut(wr)
      i += 1
    }
  }

  private[this] final def reduce(ri: RuleImpl, c1: Cell, c2: Cell, cells: Array[Cell]): Unit = {
    var i = 0
    while(i < ri.protoCells.length) {
      cells(i) = ri.protoCells(i).createCell
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
      val ri2 = ri.ruleImpls(i)
      if(ri2 != null) addCut(w, ri2)
      i += 1
    }

    @inline def cutTarget(i: Int) = if(i < c1.arity) c1.auxRefs(i) else c2.auxRefs(i-c1.arity)

    // Connect cut wire to new cell
    @inline
    def connectFreeToInternal(cIdx: Int, cp: Int, cutIdx: Int): Unit = {
      val wr = cutTarget(cutIdx)
      if(wr.connect(cells(cIdx), cp))
        createCut(wr)
    }

    // Connect 2 cut wires
    @inline
    def connectFreeToFree(cutIdx1: Int, cutIdx2: Int): Unit = {
      val wr1 = cutTarget(cutIdx1)
      val wr2 = cutTarget(cutIdx2)
      val (wt, wp) = wr1.opposite
      if(wr2.connect(wt, wp)) createCut(wr2)
    }

    i = 0
    while(i < ri.freeWires.length) {
      val fw = ri.freeWires(i)
      if(fw >= 0) connectFreeToInternal(fw, ri.freePorts(i), i)
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
