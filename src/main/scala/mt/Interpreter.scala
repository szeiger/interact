package de.szeiger.interact.mt

import de.szeiger.interact.{AST, BaseInterpreter, CheckedRule, Symbol, Symbols}

import java.io.PrintStream
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

import BitOps._

sealed trait WireOrCell

object Wire {
  def apply(): WireRef = {
    val a = new AtomicInteger()
    val w1 = new WireRef(null, 0, a)
    val w2 = new WireRef(null, 0, a)
    w1.oppo = w2
    w2.oppo = w1
    // Atomic write after construction for safe publication of oppo fields
    a.set(0)
    w1
  }
  def apply(c1: Cell, p1: Int, c2: Cell, p2: Int): WireRef = {
    val a = new AtomicInteger()
    val w1 = new WireRef(c1, p1, a)
    val w2 = new WireRef(c2, p2, a)
    w1.oppo = w2
    w2.oppo = w1
    c1.connect(p1, w1)
    c2.connect(p2, w2)
    // Atomic write after construction for safe publication of oppo fields
    a.set((if(p1 == 0) 1 else 0) + (if(p2 == 0) 1 else 0))
    w1
  }
}

final class WireRef(var cell: Cell, var cellPort: Int, principals: AtomicInteger) extends WireOrCell {
  var oppo: WireRef = _
  @inline def connectInc(t: Cell, p: Int): Int = {
    cell = t;
    cellPort = p
    if(p == 0) principals.incrementAndGet() else -1
  }
  @inline def opposite: (Cell, Int) = (oppo.cell, oppo.cellPort)
  def getPrincipals = principals.get
}

final class Cell(val sym: Symbol, val symId: Int, val arity: Int) extends WireOrCell {
  var pref: WireRef = _
  val auxRefs = new Array[WireRef](arity)
  @inline def connect(slot: Int, w: WireRef) = {
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

  @inline def connectInc(t1: Cell, p1: Int, wr2: WireRef): Int = {
    t1.connect(p1, wr2)
    wr2.connectInc(t1, p1)
  }

  def add(cuts: Iterable[AST.Cut], syms: Symbols): Unit = {
    def connectAny(t1: WireOrCell, p1: Int, t2: WireOrCell, p2: Int): Unit = {
      (t1, t2) match {
        case (t1: WireRef, t2: Cell) =>
          connectInc(t2, p2, t1)
        case (t1: Cell, t2: WireRef) =>
          connectInc(t1, p1, t2)
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
                val w = Wire()
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
            case (BoundaryTarget(c2), 0) => c = c2; acc += 1
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

  object BoundaryTarget {
    def unapply(c: Cell): Option[Cell] = {
      if(c.sym.id.s == "$Boundary" && c.arity == 1) {
        val (c1, p1) = c.getCell(1)
        if(p1 == 0) Some(c1) else None
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
      case BoundaryTarget(c1) => show(c1)
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
  final val connections: Array[Int], final val ruleImpls: Array[RuleImpl]) {
  def symIdForCell(idx: Int) = protoCells(idx).symId
  def log(): Unit = {
    if(cr == null)
      println("<boundaryRuleImpl>")
    else {
      println("  Proto cells:")
      protoCells.foreach(pc => println(s"  - $pc"))
      println("  Free wires:")
      freeWires.zip(freePorts).foreach { case (w, p) => println(s"  - ($w, $p)") }
      println("  Connections:")
      connections.zip(ruleImpls).foreach { case (c, ri) => println(s"  - ${Seq(byte0(c), byte1(c), byte2(c), byte3(c)).mkString(",")}: $ri")}
    }
  }
  override def toString = if(cr == null) "<boundaryRuleImpl>" else cr.show
}

final class Interpreter(globals: Symbols, rules: Iterable[CheckedRule], numThreads: Int) extends Scope with BaseInterpreter { self =>
  private[this] final val boundarySym = new Symbol(new AST.Ident("$Boundary"))
  private[this] final val allSymbols = globals.symbols ++ Seq(boundarySym)
  private[this] final val symIds = mutable.HashMap.from[Symbol, Int](allSymbols.zipWithIndex.map { case (s, i) => (s, i+1) })
  private[this] final val boundarySymId = symIds(boundarySym)
  private[this] final val symBits = {
    val sz = symIds.size
    val high = Integer.highestOneBit(sz)
    if(sz == high) Integer.numberOfTrailingZeros(high) else Integer.numberOfTrailingZeros(high)+1
  }

  override def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)

  private[this] final val boundaryRuleImpl = new RuleImpl(null, null, null, null, null, null)
  private[this] final val ruleImpls = new Array[RuleImpl](1 << (symBits << 1))
  private[this] final val maxRuleCells = createRuleImpls()

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
      val ri = createRuleImpl(cr, cr.r.reduced,
        if(s1id <= s2id) s1id else s2id, if(s1id <= s2id) s2id else s1id,
        if(s1id <= s2id) cr.args1 else cr.args2, if(s1id <= s2id) cr.args2 else cr.args1,
        globals)
      //ri.log()
      if(ri.protoCells.length > max) max = ri.protoCells.length
      ruleImpls(rk) = ri
      ris.addOne(ri)
    }
    val allConss = symIds.iterator.filter(s => s._1.isCons || s._2 == boundarySymId).map(_._2)
    allConss.foreach(s => ruleImpls(mkRuleKey(s, boundarySymId)) = boundaryRuleImpl)
    ris.foreach { ri =>
      ri.connections.zipWithIndex.foreach { case (IntOfBytes(t1, p1, t2, p2), i) =>
        if(p1 == 0 && p2 == 0)
          ri.ruleImpls(i) = ruleImpls(mkRuleKey(ri.symIdForCell(t1), ri.symIdForCell(t2)))
      }
    }
    max
  }

  def createRuleImpl(cr: CheckedRule, reduced: Seq[AST.Cut], symId1: Int, symId2: Int, args1: Seq[AST.Ident], args2: Seq[AST.Ident], globals: Symbols): RuleImpl = {
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

    new RuleImpl(cr, protoCells, freeWires, freePorts, conns.toArray, new Array(conns.size))
  }

  @inline def mkRuleKey(w: WireRef): Int =
    mkRuleKey(w.cell.symId, w.oppo.cell.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  private[this] final class InterpreterThread extends (((WireRef, RuleImpl)) => Unit) {
    private[Interpreter] var nextCut: WireRef = null
    private[Interpreter] var nextRule: RuleImpl = null
    private[this] final val tempCells = new Array[Cell](maxRuleCells)
    private[Interpreter] var steps = 0

    def addCut(w: WireRef, ri: RuleImpl): Unit = {
      //println(s"Adding cut on $w using $ri")
      if(nextCut == null) { nextCut = w; nextRule = ri }
      else queue.addOne((w, ri))
    }

    @inline def createCut(t: WireRef): Unit = {
      val ri = ruleImpls(mkRuleKey(t))
      //println(s"createCut ${t.leftCell.sym} . ${t.rightCell.sym} = $ri")
      if(ri != null) addCut(t, ri)
    }

    def removeBoundary(cut: WireRef): Unit = {
      val (b, o) = if(cut.cell.symId == boundarySymId) (cut.cell, cut.oppo.cell) else (cut.oppo.cell,cut.cell)
      val wr = b.auxRefs(0)
      if(connectInc(o, 0, wr) == 2) createCut(wr)
    }

    def reduce(ri: RuleImpl, c1: Cell, c2: Cell, cells: Array[Cell]): Unit = {
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
        val w = Wire(t1, p1, t2, p2)
        val ri2 = ri.ruleImpls(i)
        if(ri2 != null) addCut(w, ri2)
        i += 1
      }

      @inline def cutTarget(i: Int) = if(i < c1.arity) c1.auxRefs(i) else c2.auxRefs(i-c1.arity)

      // Connect cut wire to new cell
      @inline
      def connectFreeToInternal(cIdx: Int, cp: Int, cutIdx: Int): Unit = {
        val wr = cutTarget(cutIdx)
        if(connectInc(cells(cIdx), cp, wr) == 2) createCut(wr)
      }

      // Connect 2 cut wires
      @inline
      def connectFreeToFree(cutIdx1: Int, cutIdx2: Int): Unit = {
        val wr1 = cutTarget(cutIdx1)
        val wr2 = cutTarget(cutIdx2)
        if(wr1.getPrincipals == 1) { // take ownership of opposing cell on t
          val (wt, wp) = wr1.opposite
          if(connectInc(wt, wp, wr2) == 2) createCut(wr2)
        } else if(wr2.getPrincipals == 1) { // take ownership of opposing cell on t2
          val (wt, wp) = wr2.opposite
          if(connectInc(wt, wp, wr1) == 2) createCut(wr1)
        } else { // ownership unclear -> insert boundary
          val b = new Cell(boundarySym, boundarySymId, 1)
          connectInc(b, 1, wr2)
          if(connectInc(b, 0, wr1) == 2) createCut(wr1)
        }
      }

      i = 0
      while(i < ri.freeWires.length) {
        val fw = ri.freeWires(i)
        if(fw >= 0) connectFreeToInternal(fw, ri.freePorts(i), i)
        else if(i < -1-fw) connectFreeToFree(i, -1-fw)
        i += 1
      }
    }

    def processLocalCut(): Unit = {
      //println(s"Remaining reducible cuts: ${cuts.size+1}")
      steps += 1
      val c = nextCut
      //println(s"Reducing $c with ${c.ruleImpl}")
      //c.ruleImpl.log()
      nextCut = null
      val ri = nextRule
      if(ri eq boundaryRuleImpl) removeBoundary(c)
      else {
        val (c1, c2) = if(c.cell.symId <= c.oppo.cell.symId) (c.cell, c.oppo.cell) else (c.oppo.cell, c.cell)
        reduce(ri, c1, c2, tempCells)
      }
      //validate()
      //println("After reduction:")
      //log()
    }

    def apply(data: (WireRef, RuleImpl)): Unit = {
      assert(nextCut == null)
      nextCut = data._1
      nextRule = data._2
      while(nextCut != null) processLocalCut()
    }
  }

  def detectInitialCuts(): Unit = {
    val detected = mutable.HashSet.empty[WireRef]
    reachableCells.foreach { c =>
      val w = c.pref
      val ri = ruleImpls(mkRuleKey(w))
      if(ri != null) {
        if(w.cellPort == 0 && w.oppo.cellPort == 0 && !detected.contains(w.oppo)) {
          detected.addOne(w)
          queue.addOne((w, ri))
        }
      }
    }
  }

  // Used by the debugger
  def getRuleImpl(w: WireRef): RuleImpl = ruleImpls(mkRuleKey(w))
  def reduce1(w: WireRef): Unit = {
    queue.clear()
    val t = new InterpreterThread()
    t.nextCut = w
    t.nextRule = getRuleImpl(w)
    t.processLocalCut()
  }

  private[this] val workerThreads = (0 until 1.max(numThreads)).map(_ => new InterpreterThread).toSeq
  private[this] val pool = if(numThreads == 0) null else new Workers[(WireRef, RuleImpl)](workerThreads)
  private[this] val queue: mutable.Growable[(WireRef, RuleImpl)] = if(numThreads == 0) mutable.ArrayBuffer.empty else pool

  def reduce(): Int = {
    //validate()
    detectInitialCuts()
    if(numThreads == 0) {
      val w = workerThreads(0)
      val queue = this.queue.asInstanceOf[mutable.ArrayBuffer[(WireRef, RuleImpl)]]
      while(!queue.isEmpty) {
        val c = queue.last
        queue.dropRightInPlace(1)
        w.apply(c)
      }
    } else {
      pool.start()
      pool.awaitEmpty()
      pool.shutdown()
    }
    //log()
    //println(steps)
    workerThreads.iterator.map(_.steps).sum
  }
}

object BitOps {
  @inline def byte0(i: Int): Int = (i & 0xFF).toByte
  @inline def byte1(i: Int): Int = ((i >>> 8) & 0xFF).toByte
  @inline def byte2(i: Int): Int = ((i >>> 16) & 0xFF).toByte
  @inline def byte3(i: Int): Int = ((i >>> 24) & 0xFF).toByte
  @inline def intOfBytes(b0: Int, b1: Int, b2: Int, b3: Int): Int = b0.toByte&0xFF | ((b1.toByte&0xFF) << 8) | ((b2.toByte&0xFF) << 16) | ((b3.toByte&0xFF) << 24)
  def checkedIntOfBytes(b0: Int, b1: Int, b2: Int, b3: Int): Int = {
    assert(b0 >= -128 && b0 <= 127)
    assert(b1 >= -128 && b1 <= 127)
    assert(b2 >= -128 && b2 <= 127)
    assert(b3 >= -128 && b3 <= 127)
    intOfBytes(b0, b1, b2, b3)
  }

  object IntOfBytes {
    @inline def unapply(i: Int): Some[(Int, Int, Int, Int)] = Some((byte0(i), byte1(i), byte2(i), byte3(i)))
  }
}
