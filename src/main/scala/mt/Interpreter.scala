package de.szeiger.interact.mt

import de.szeiger.interact.{AST, BaseInterpreter, CheckedRule, Symbol, Symbols}

import java.io.PrintStream
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

import BitOps._

sealed trait WireOrCell

final class Wire(_leftCell: Cell, _leftPort: Int, _rightCell: Cell, _rightPort: Int)
    extends WireRef(null, false, _leftCell, _leftPort, new AtomicInteger((if(_leftCell != null && _leftPort == 0) 1 else 0) + (if(_rightCell != null && _rightPort == 0) 1 else 0)))
    with WireOrCell {
  @inline def ref0: WireRef = this
  final val ref1: WireRef = new WireRef(this, true, _rightCell, _rightPort, principals)
  @inline def ref(p: Boolean): WireRef = if(p) ref1 else ref0
  var ruleImpl: RuleImpl = _
  //@jdk.internal.vm.annotation.Contended
  def validate(): Unit = {
    if(ref0.cell != null) assert(ref0.cell.getWireRef(ref0.cellPort) == ref0)
    if(ref1.cell != null) assert(ref1.cell.getWireRef(ref1.cellPort) == ref1)
    assert(principals.get() == ref0.principalCount + ref1.principalCount)
  }
  override def toString = s"Wire(${ref0.cell}, ${ref0.cellPort}, ${ref1.cell}, ${ref1.cellPort}, ${principals.get()})"
}

class WireRef(_w: Wire, val p: Boolean, var cell: Cell, var cellPort: Int, protected[this] val principals: AtomicInteger) {
  val w: Wire = if(_w == null) this.asInstanceOf[Wire] else _w
  def connectInc(t: Cell, p: Int): Int = {
    cell = t;
    cellPort = p
    if(p == 0) incPrincipals else -1
  }
  @inline def opposite: (Cell, Int) = {
    val o = w.ref(!p)
    (o.cell, o.cellPort)
  }
  def principalCount = if(cellPort == 0 && cell != null) 1 else 0
  def getPrincipals = principals.get
  def resetPrincipals: Unit = principals.set(0)
  def incPrincipals = principals.incrementAndGet()
}

object Wire {
  def unapply(w: Wire): Some[(Cell, Int, Cell, Int)] = Some((w.ref0.cell, w.ref0.cellPort, w.ref1.cell, w.ref1.cellPort))
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
  @inline def getCell(p: Int): (Cell, Int) = {
    val w = getWireRef(p)
    if(w == null) null else w.opposite
  }
  def allPorts: Iterator[WireRef] = Iterator.single(pref) ++ auxRefs.iterator
  def allCells: Iterator[(WireRef, (Cell, Int))] = (0 to arity).iterator.map { i => (getWireRef(i), getCell(i)) }
  override def toString = s"Cell($sym, $symId, $arity, ${allPorts.map { case w => s"(${if(w.w == null) "null" else "_"},${w.p})" }.mkString(", ") })"
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
        case (t1: Wire, t2: Cell) =>
          connectInc(t2, p2, t1.ref(p1 != 0))
        case (t1: Cell, t2: Wire) =>
          connectInc(t1, p1, t2.ref(p2 != 0))
        case (t1: Cell, t2: Cell) =>
          val w = new Wire(t1, p1, t2, p2)
          t1.connect(p1, w.ref0)
          t2.connect(p2, w.ref1)
      }
    }
    addSymbols(cuts, syms)
    val bind = mutable.HashMap.empty[Symbol, Wire]
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
                val w = new Wire(null, 0, null, 0)
                w.resetPrincipals
                bind.put(s, w)
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
            //val (at, ap) = create(a)
            //connectAny(c, p, at, ap)
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
    val wires =  reachableCells.flatMap(_.allPorts).map(_.w).toSet
    wires.foreach(_.validate())
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

  def getCutLogs(): Iterator[(Wire, String, String, Option[String])] = {
    val freeWireNames = freeWires.map(_.sym.toString)
    val cuts = mutable.HashSet.from(reachableCells.filter(_.getCell(0)._2 == 0)).map { c =>
      val w1 = c.pref.w
      val w2 = c.getCell(0)._1.pref.w
      assert(w1 == w2)
      c.pref.w
    }
    var nextTemp = -1
    val helpers = mutable.Map.empty[Wire, String]
    def explicit(w: Wire): String = helpers.getOrElseUpdate(w, {
      nextTemp += 1
      "$" + nextTemp
    })
    def targetOrReplacement(w: Wire, t: Cell, p: Int): String = helpers.get(w) match {
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
      case c => c.allCells.drop(1).map { case (wr, (t, p)) => targetOrReplacement(wr.w, t, p) }.mkString(s"${c.sym}(", ", ", ")")
    }
    val strs = cuts.iterator.map { case w @ Wire(c1, _, c2, _) =>
      if(c1.symId == 0) (w, c1.sym.toString, show(c2), None)
      else if(c2.symId == 0) (w, c2.sym.toString, show(c1), None)
      else (w, explicit(w), show(c1), Some(show(c2)))
    }
    strs.zipWithIndex.toIndexedSeq.sortBy { case ((w, l, r, o), idx) =>
      val f = freeWireNames.contains(l)
      (!f, if(f) l else "", idx)
    }.iterator.map(_._1)
  }

  def log(out: PrintStream): Unit = {
    getCutLogs().foreach { case (w, l, r, o) =>
      val c = if(w.ruleImpl != null) "*" else "."
      out.println(s"  ${l} $c ${r}")
      o.foreach(r2 => out.println(s"  ${l} $c ${r2}"))
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
  cut1SymId: Int, cut2SymId: Int) {
  def symIdForCell(idx: Int) =
    if(idx == protoCells.length) cut1SymId
    else if(idx == protoCells.length+2) cut2SymId
    else protoCells(idx).symId
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

  private[this] final val boundaryRuleImpl = new RuleImpl(null, null, null, null, null, null, -1, -1)
  private[this] final val ruleImpls = new Array[RuleImpl](1 << (symBits << 1))
  private[this] final val (maxRuleCells, maxCutArity) = createRuleImpls()

  def createRuleImpls(): (Int, Int) = {
    val ris = new ArrayBuffer[RuleImpl]()
    var max, maxA = 0
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
      if(s1.cons.arity > maxA) maxA = s1.cons.arity
      if(s2.cons.arity > maxA) maxA = s2.cons.arity
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
    (max + 2, maxA * 2)
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

    val reuse1 = cells.indexWhere(c => c.symId == symId1)
    val reuse1c = if(reuse1 == -1) null else cells(reuse1)
    val reuse2 = cells.indexWhere(c => c.symId == symId2 && c != reuse1c)
    val reuse2c = if(reuse2 == -1) null else cells(reuse2)
    val remapIndices = new Array[Int](cells.length)
    var i, j = 0
    val reuseOffset = (if(reuse1 == -1) 0 else 1) + (if(reuse2 == -1) 0 else 1)
    while(i < cells.length) {
      if(i == reuse1) remapIndices(i) = cells.length - reuseOffset
      else if(i == reuse2) remapIndices(i) = cells.length + 1 - reuseOffset
      else {
        remapIndices(i) = j
        j += 1
      }
      i += 1
    }
    val remap = remapIndices.zipWithIndex.map { case (i, j) => (j, i) }.toMap
    //println(s"In ${cr.show}: resuse1c = $reuse1c, reuse2c = $reuse2c")
    val protoCells2 = protoCells.zipWithIndex.filter { case (_, i) => i != reuse1 && i != reuse2 }.map(_._1)
    val freeWires2 = freeWires.map(w => if(w >= 0) remap(w) else w)
    val conns2 = conns.map { case IntOfBytes(i, j, w, p) =>
      checkedIntOfBytes(remap(i), j, if(w >= 0) remap(w) else w, p)
    }
    new RuleImpl(cr, protoCells2, freeWires2, freePorts, conns2.toArray, new Array(conns.size),
      if(reuse1c == null) -1 else reuse1c.symId, if(reuse2c == null) -1 else reuse2c.symId)
  }

  @inline def mkRuleKey(w: Wire): Int =
    mkRuleKey(w.ref0.cell.symId, w.ref1.cell.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  private[this] final class InterpreterThread extends (Wire => Unit) {
    private[Interpreter] var nextCut: Wire = null
    private[this] final val tempCells = new Array[Cell](maxRuleCells)
    private[this] final val tempWireRefs = new Array[WireRef](maxCutArity)
    private[Interpreter] var steps = 0

    def addCut(w: Wire, ri: RuleImpl): Unit = {
      //println(s"Adding cut on $w using $ri")
      w.ruleImpl = ri
      assert(w != null)
      if(nextCut == null) nextCut = w
      else queue.addOne(w)
    }

    @inline def createCut(t: Wire): Unit = {
      val ri = ruleImpls(mkRuleKey(t))
      //println(s"createCut ${t.leftCell.sym} . ${t.rightCell.sym} = $ri")
      if(ri != null) addCut(t, ri)
    }

    def removeBoundary(cut: Wire): Unit = {
      val (b, o) = if(cut.ref0.cell.symId == boundarySymId) (cut.ref0.cell, cut.ref1.cell) else (cut.ref1.cell,cut.ref0.cell)
      val wr = b.auxRefs(0)
      if(connectInc(o, 0, wr) == 2) createCut(wr.w)
    }

    def reduce(ri: RuleImpl, c1: Cell, c2: Cell, cells: Array[Cell], tempWireRefs: Array[WireRef]): Unit = {
      System.arraycopy(c1.auxRefs, 0, tempWireRefs, 0, c1.auxRefs.length)
      System.arraycopy(c2.auxRefs, 0, tempWireRefs, c1.auxRefs.length, c2.auxRefs.length)
      var i = 0
      while(i < ri.protoCells.length) {
        cells(i) = ri.protoCells(i).createCell
        i += 1
      }
      cells(i) = c1
      i += 1
      cells(i) = c2
      i = 0
      while(i < ri.connections.length) {
        val conn = ri.connections(i)
        val t1 = cells(byte0(conn))
        val p1 = byte1(conn)
        val t2 = cells(byte2(conn))
        val p2 = byte3(conn)
        val w = new Wire(t1, p1, t2, p2)
        t1.connect(p1, w.ref0)
        t2.connect(p2, w.ref1)
        val ri2 = ri.ruleImpls(i)
        if(ri2 != null) addCut(w, ri2)
        i += 1
      }

      // Connect cut wire to new cell
      @inline
      def connectFreeToInternal(fw: Int, wr: WireRef): Unit = {
        val cp = ri.freePorts(i)
        if(connectInc(cells(fw), cp, wr) == 2) createCut(wr.w)
      }

      // Connect 2 cut wires
      @inline
      def connectFreeToFree(wr: WireRef, wr2: WireRef): Unit = {
        if(wr.getPrincipals == 1) { // take ownership of opposing cell on t
          val (wt, wp) = wr.opposite
          if(connectInc(wt, wp, wr2) == 2) createCut(wr2.w)
        } else if(wr2.getPrincipals == 1) { // take ownership of opposing cell on t2
          val (wt, wp) = wr2.opposite
          if(connectInc(wt, wp, wr) == 2) createCut(wr.w)
        } else { // ownership unclear -> insert boundary
          val b = new Cell(boundarySym, boundarySymId, 1)
          connectInc(b, 1, wr2)
          if(connectInc(b, 0, wr) == 2) createCut(wr.w)
        }
      }

      i = 0
      while(i < ri.freeWires.length) {
        val fw = ri.freeWires(i)
        val wr = tempWireRefs(i)
        if(fw >= 0) connectFreeToInternal(fw, wr)
        else if(i < -1-fw) connectFreeToFree(wr, tempWireRefs(-1-fw))
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
      if(c.ruleImpl eq boundaryRuleImpl) removeBoundary(c)
      else {
        val (c1, c2) = if(c.ref0.cell.symId <= c.ref1.cell.symId) (c.ref0.cell, c.ref1.cell) else (c.ref1.cell, c.ref0.cell)
        reduce(c.ruleImpl, c1, c2, tempCells, tempWireRefs)
      }
      //validate()
      //println("After reduction:")
      //log()
    }

    def apply(w: Wire): Unit = {
      assert(nextCut == null)
      nextCut = w
      while(nextCut != null) processLocalCut()
    }
  }

  def detectInitialCuts(): Unit = {
    reachableCells.foreach { c =>
      val w = c.pref.w
      if(w.ruleImpl == null && w.ref0.cellPort == 0 && w.ref1.cellPort == 0) {
        val ri = ruleImpls(mkRuleKey(w))
        if(ri != null) {
          w.ruleImpl = ri
          queue.addOne(w)
        }
      }
    }
  }

  def reduce1(w: Wire): Unit = {
    queue.clear()
    val t = new InterpreterThread()
    t.nextCut = w
    t.processLocalCut()
  }

  private[this] val workerThreads = (0 until 1.max(numThreads)).map(_ => new InterpreterThread).toSeq
  private[this] val pool = if(numThreads == 0) null else new Workers[Wire](workerThreads)
  private[this] val queue: mutable.Growable[Wire] = if(numThreads == 0) mutable.ArrayBuffer.empty[Wire] else pool

  def reduce(): Int = {
    //validate()
    detectInitialCuts()
    if(numThreads == 0) {
      val w = workerThreads(0)
      val queue = this.queue.asInstanceOf[mutable.ArrayBuffer[Wire]]
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
  @inline def byte1(i: Int): Int = ((i & (0xFF << 8)) >>> 8).toByte
  @inline def byte2(i: Int): Int = ((i & (0xFF << 16)) >>> 16).toByte
  @inline def byte3(i: Int): Int = ((i & (0xFF << 24)) >>> 24).toByte
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
