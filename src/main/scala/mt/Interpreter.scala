package de.szeiger.interact.mt

import de.szeiger.interact.{AST, BaseInterpreter, CheckedRule, Symbol, Symbols}

import java.io.PrintStream
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

import BitOps._

sealed abstract class WireOrCell

final class Wire(var leftCell: Cell, var leftPort: Int, var rightCell: Cell, var rightPort: Int) extends WireOrCell {
  var ruleImpl: RuleImpl = _
  private[this] val principals = new AtomicInteger((if(leftCell != null && leftPort == 0) 1 else 0) + (if(rightCell != null && rightPort == 0) 1 else 0))
  def getPrincipals = principals.get
  def resetPrincipals: Unit = principals.set(0)
  def incPrincipals = principals.incrementAndGet()
  @inline def connect(slot: Int, t: Cell, p: Int): Unit = {
    if(slot == 0) { leftCell = t; leftPort = p }
    else { rightCell = t; rightPort = p }
  }
  @inline def getOppositeCellAndPort(i: Int): (Cell, Int) =
    if(i == 0) (rightCell, rightPort) else (leftCell, leftPort)
  def validate(): Unit = {
    if(leftCell != null) assert(leftCell.getWireAndPort(leftPort) == (this, 0))
    if(rightCell != null) assert(rightCell.getWireAndPort(rightPort) == (this, 1))
    assert(principals.get() == (if(leftCell != null && leftPort == 0) 1 else 0) + (if(rightCell != null && rightPort == 0) 1 else 0))
  }
  override def toString = s"Wire($leftCell, $leftPort, $rightCell, $rightPort, ${principals.get()})"
}

object Wire {
  def unapply(w: Wire): Some[(Cell, Int, Cell, Int)] = Some((w.leftCell, w.leftPort, w.rightCell, w.rightPort))
}

final class Cell(val sym: Symbol, val symId: Int, val arity: Int) extends WireOrCell {
  var ptarget: Wire = _
  var pport: Int = _
  val auxTargets = new Array[Wire](arity)
  val auxPorts = new Array[Int](arity)
  def connect(slot: Int, t: Wire, p: Int) = {
    if(slot == 0) { ptarget = t; pport = p }
    else {
      auxTargets(slot-1) = t
      auxPorts(slot-1) = p
    }
  }
  def getWireAndPort(slot: Int): (Wire, Int) =
    if(slot == 0) (ptarget, pport)
    else (auxTargets(slot-1), auxPorts(slot-1))
  @inline def getCell(p: Int): (Cell, Int) = {
    val (w, wp) = if(p == 0) (ptarget, pport) else (auxTargets(p-1), auxPorts(p-1))
    if(w == null) null
    else w.getOppositeCellAndPort(wp)
  }
  def allPorts: Iterator[(Wire, Int)] = Iterator.single((ptarget, pport)) ++ auxTargets.iterator.zip(auxPorts.iterator)
  def allCells: Iterator[((Wire, Int), (Cell, Int))] = (0 to arity).iterator.map { i => (getWireAndPort(i), getCell(i)) }
  override def toString = s"Cell($sym, $symId, $arity, ${allPorts.map { case (t, p) => s"(${if(t == null) "null" else "_"},$p)" }.mkString(", ") })"
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

  @inline def connect(t1: Cell, p1: Int, t2: Wire, p2: Int): Unit = {
    t1.connect(p1, t2, p2)
    t2.connect(p2, t1, p1)
  }

  def add(cuts: Iterable[AST.Cut], syms: Symbols): Unit = {
    def connectAny(t1: WireOrCell, p1: Int, t2: WireOrCell, p2: Int): Unit = {
      (t1, t2) match {
        case (t1: Wire, t2: Cell) =>
          connect(t2, p2, t1, p1)
          if(p2 == 0) t1.incPrincipals
        case (t1: Cell, t2: Wire) =>
          connect(t1, p1, t2, p2)
          if(p1 == 0) t2.incPrincipals
        case (t1: Cell, t2: Cell) =>
          val w = new Wire(t1, p1, t2, p2)
          t1.connect(p1, w, 0)
          t2.connect(p2, w, 1)
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
    val wires =  reachableCells.flatMap(_.allPorts).map(_._1).toSet
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
      val w1 = c.ptarget
      val w2 = c.getCell(0)._1.ptarget
      assert(w1 == w2)
      c.ptarget
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
      case c => c.allCells.drop(1).map { case ((w, _), (t, p)) => targetOrReplacement(w, t, p) }.mkString(s"${c.sym}(", ", ", ")")
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

final class RuleImpl(cr: CheckedRule, final val protoCells: Array[ProtoCell], final val freeWires: Array[Int], final val freePorts: Array[Int], final val connections: Array[Int], final val ruleImpls: Array[RuleImpl]) {
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

final class Interpreter(globals: Symbols, rules: Iterable[CheckedRule]) extends Scope with BaseInterpreter { self =>
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
      val s1 = getSymbolId(globals(cr.name1))
      val s2 = getSymbolId(globals(cr.name2))
      val rk = mkRuleKey(s1, s2)
      val ri = createRuleImpl(cr, cr.r.reduced, if(s1 <= s2) cr.args1 else cr.args2, if(s1 <= s2) cr.args2 else cr.args1, globals)
      //ri.log()
      if(ri.protoCells.length > max) max = ri.protoCells.length
      ruleImpls(rk) = ri
      ris.addOne(ri)
    }
    val allConss = symIds.iterator.filter(s => s._1.isCons || s._2 == boundarySymId).map(_._2)
    allConss.foreach(s => ruleImpls(mkRuleKey(s, boundarySymId)) = boundaryRuleImpl)
    ris.foreach { ri =>
      ri.connections.zipWithIndex.foreach { case (c, i) =>
        val t1 = byte0(c)
        val p1 = byte1(c)
        val t2 = byte2(c)
        val p2 = byte3(c)
        val pc = ri.protoCells(t1)
        val pc2 = ri.protoCells(t2)
        if(p1 == 0 && p2 == 0)
          ri.ruleImpls(i) = ruleImpls(mkRuleKey(pc.symId, pc2.symId))
      }
    }
    max
  }

  def createRuleImpl(cr: CheckedRule, reduced: Seq[AST.Cut], args1: Seq[AST.Ident], args2: Seq[AST.Ident], globals: Symbols): RuleImpl = {
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

  @inline def mkRuleKey(w: Wire): Int =
    mkRuleKey(w.leftCell.symId, w.rightCell.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  private[this] final class InterpreterThread extends (Wire => Unit) {
    private[Interpreter] var nextCut: Wire = null
    private[this] final val tempCells = new Array[Cell](maxRuleCells)
    private[Interpreter] var steps = 0

    def addCut(w: Wire, ri: RuleImpl): Unit = {
      //println(s"Adding cut on $w using $ri")
      w.ruleImpl = ri
      if(nextCut == null) nextCut = w
      else queue.addOne(w)
    }

    @inline def createCut(t: Wire): Unit = {
      val ri = ruleImpls(mkRuleKey(t))
      //println(s"createCut ${t.leftCell.sym} . ${t.rightCell.sym} = $ri")
      if(ri != null) addCut(t, ri)
    }

    def removeBoundary(cut: Wire): Unit = {
      val (b, o) = if(cut.leftCell.symId == boundarySymId) (cut.leftCell, cut.rightCell) else (cut.rightCell,cut.leftCell)
      val w = b.auxTargets(0)
      connect(o, 0, w, b.auxPorts(0))
      if(w.incPrincipals == 2) createCut(w)
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
        val ri2 = ri.ruleImpls(i)
        val w = new Wire(t1, p1, t2, p2)
        t1.connect(p1, w, 0)
        t2.connect(p2, w, 1)
        if(ri2 != null) addCut(w, ri2)
        i += 1
      }
      i = 0
      @inline def cutTarget(i: Int) =
        if(i < c1.arity) (c1.auxTargets(i), c1.auxPorts(i)) else (c2.auxTargets(i-c1.arity), c2.auxPorts(i-c1.arity))
      while(i < ri.freeWires.length) {
        val fw = ri.freeWires(i)
        val (t, p) = cutTarget(i)
        if(fw >= 0) { // Connect cut wire to new cell
          val (ct, cp) = (cells(fw), ri.freePorts(i))
          connect(ct, cp, t, p)
          if(cp == 0 && t.incPrincipals == 2)
            createCut(t)
        } else if(i < -1-fw) { // Connect 2 cut wires
          val (t2, p2) = cutTarget(-1-fw)
          // Always remove one wire (not mt-safe)
          //val (wt, wp) = t2.getOppositeCellAndPort(p2)
          //connect(wt, wp, t, p)
          //if(wp == 0 && t.principals.incrementAndGet() == 2)
          if(t.getPrincipals == 1) { // take ownership of opposing cell on t
            val (wt, wp) = t.getOppositeCellAndPort(p)
            connect(wt, wp, t2, p2)
            if(wp == 0 && t2.incPrincipals == 2) createCut(t2)
          } else if(t2.getPrincipals == 1) { // take ownership of opposing cell on t2
            val (wt, wp) = t2.getOppositeCellAndPort(p2)
            connect(wt, wp, t, p)
            if(wp == 0 && t.incPrincipals == 2) createCut(t)
          } else { // ownership unclear -> insert boundary
            val b = new Cell(boundarySym, boundarySymId, 1)
            connect(b, 0, t, p)
            connect(b, 1, t2, p2)
            if(t.incPrincipals == 2) createCut(t)
          }
        }
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
        val (c1, c2) = if(c.leftCell.symId <= c.rightCell.symId) (c.leftCell, c.rightCell) else (c.rightCell, c.leftCell)
        reduce(c.ruleImpl, c1, c2, tempCells)
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
      val w = c.ptarget
      if(w.ruleImpl == null && w.leftPort == 0 && w.rightPort == 0) {
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

  private[this] val workerThreads = (0 until 1).map(_ => new InterpreterThread)

  private[this] val pool = new Workers[Wire](workerThreads)
  private[this] val queue: mutable.Growable[Wire] = pool
  def reduce(): Int = {
    //validate()
    detectInitialCuts()
    pool.start()
    pool.awaitEmpty()
    pool.shutdown()
    //log()
    //println(steps)
    workerThreads.iterator.map(_.steps).sum
  }

//  private[this] val queue = mutable.ArrayBuffer.empty[Wire]
//  def reduce(): Int = {
//    //validate()
//    detectInitialCuts()
//    val w = workerThreads(0)
//    while(!queue.isEmpty) {
//      val c = queue.last
//      queue.dropRightInPlace(1)
//      w.apply(c)
//    }
//    //log()
//    //println(steps)
//    workerThreads.iterator.map(_.steps).sum
//  }
}

object BitOps {
  @inline def byte0(i: Int): Int = i & 0xFF
  @inline def byte1(i: Int): Int = (i & (0xFF << 8)) >>> 8
  @inline def byte2(i: Int): Int = (i & (0xFF << 16)) >>> 16
  @inline def byte3(i: Int): Int = (i & (0xFF << 24)) >>> 24
  @inline def intOfBytes(b0: Int, b1: Int, b2: Int, b3: Int): Int = b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
  def checkedIntOfBytes(b0: Int, b1: Int, b2: Int, b3: Int): Int = {
    assert(b0 <= 255)
    assert(b1 <= 255)
    assert(b2 <= 255)
    assert(b3 <= 255)
    intOfBytes(b0, b1, b2, b3)
  }
}