package de.szeiger.interact.mt

import de.szeiger.interact.{AST, Symbol, Symbols, CheckedRule, BaseInterpreter}
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

sealed abstract class WireOrCell

final class Wire extends WireOrCell {
  var ruleImpl: RuleImpl = _
  var leftCell: Cell = _
  var leftPort: Int = _
  var rightCell: Cell = _
  var rightPort: Int = _
  def connect(slot: Int, t: Cell, p: Int): Unit = {
    if(slot == 0) { leftCell = t; leftPort = p }
    else { rightCell = t; rightPort = p }
  }
  @inline def getCell(i: Int): (Cell, Int) =
    if(i == 0) (leftCell, leftPort) else (rightCell, rightPort)
  def validate(): Unit = {
    if(leftCell != null) assert(leftCell.getPort(leftPort) == (this, 0))
    if(rightCell != null) assert(rightCell.getPort(rightPort) == (this, 1))
  }
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
  def getPort(slot: Int): (Wire, Int) =
    if(slot == 0) (ptarget, pport)
    else (auxTargets(slot-1), auxPorts(slot-1))
  def getCell(p: Int): (Cell, Int) = {
    val (w, wp) = if(p == 0) (ptarget, pport) else (auxTargets(p-1), auxPorts(p-1))
    if(w == null) null
    else w.getCell(1-wp)
  }
  def allPorts: Iterator[(Wire, Int)] = Iterator.single((ptarget, pport)) ++ auxTargets.iterator.zip(auxPorts.iterator)
  def allCells: Iterator[((Wire, Int), (Cell, Int))] = (0 to arity).iterator.map { i => (getPort(i), getCell(i)) }
  override def toString = s"Cell($sym, $symId, $arity, ${allPorts.map { case (t, p) => s"(${if(t == null) "null" else "_"},$p)" }.mkString(", ") })"
}

class Scope {
  val freeWires = mutable.HashSet.empty[Cell]

  def getSymbolId(sym: Symbol): Int = -1

  private def addSymbols(cs: Iterable[AST.Cut], symbols: Symbols): Unit = {
    def f(e: AST.Expr): Unit = e match {
      case i: AST.Ident =>
        val s = symbols.getOrAdd(i)
        if(!s.isCons) s.refs += 1
      case AST.Ap(i, es) => f(i); es.foreach(f)
    }
    cs.foreach { c => f(c.left); f(c.right) }
  }

  @inline def connect(t1: Wire, p1: Int, t2: Cell, p2: Int): Unit =
    connect(t2, p2, t1, p1)

  @inline def connect(t1: Cell, p1: Int, t2: Wire, p2: Int): Unit = {
    t1.connect(p1, t2, p2)
    t2.connect(p2, t1, p1)
  }

  @inline def connect(t1: Wire, p1: Int, t2: Wire, p2: Int): Unit = {
    val (tc1, tp1) = t1.getCell(1-p1)
    connect(tc1, tp1, t2, p2)
  }

  @inline def connect(t1: Cell, p1: Int, t2: Cell, p2: Int): Unit = {
    val w = new Wire
    t1.connect(p1, w, 0)
    w.connect(0, t1, p1)
    t2.connect(p2, w, 1)
    w.connect(1, t2, p2)
  }

  def connect(t1: WireOrCell, p1: Int, t2: WireOrCell, p2: Int): Unit = {
    (t1, t2) match {
      case (t1: Wire, t2: Cell) => connect(t1, p1, t2, p2)
      case (t1: Wire, t2: Wire) => connect(t1, p1, t2, p2)
      case (t1: Cell, t2: Wire) => connect(t1, p1, t2, p2)
      case (t1: Cell, t2: Cell) => connect(t1, p1, t2, p2)
    }
  }

  def add(cuts: Iterable[AST.Cut], syms: Symbols): Unit = {
    addSymbols(cuts, syms)
    val bind = mutable.HashMap.empty[Symbol, Wire]
    def create(e: AST.Expr): (WireOrCell, Int) = e match {
      case i: AST.Ident =>
        val s = syms.getOrAdd(i)
        if(s.isCons) {
          val s = syms.getOrAdd(i)
          val c = new Cell(s, getSymbolId(s), s.cons.arity)
          (c, 0)
        } else if(s.refs == 1) {
          val c = new Cell(s, -1, 0)
          freeWires.addOne(c)
          (c, 0)
        } else if(s.refs == 2) {
          bind.get(s) match {
            case Some(w) => (w, 1)
            case None =>
              val w = new Wire
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
          val (at, ap) = create(a)
          connect(c, p, at, ap)
        }
        (c, 0)
    }
    def createCut(e: AST.Cut): Unit = {
      val (lt, ls) = create(e.left)
      val (rt, rs) = create(e.right)
      connect(lt, ls, rt, rs)
      connect(rt, rs, lt, ls)
    }
    cuts.foreach(createCut)
  }

  def validate(): Unit = {
    val wires =  reachableCells.flatMap(_.allPorts).map(_._1).toSet
    wires.foreach(_.validate())
  }

  object Church {
    def unapply(c: Cell): Option[Int] = {
      if(c.sym.id.s == "Z" && c.arity == 0) Some(0)
      else if(c.sym.id.s == "S" && c.arity == 1) {
        c.getCell(1) match {
          case (c2: Cell, 0) => unapply(c2).map(_ + 1)
          case _ => None
        }
      } else None
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

  def log(): Unit = {
    println(s"  Free wires: ${freeWires.map(_.sym).mkString(", ")}")
    println("  Cells:")
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
      case c if c.symId == -1 => c.sym.toString
      case ListCons(c1, c2) => s"${show(c1)} :: ${show(c2)}"
      case c =>
        c.allCells.drop(1).map { case ((w, _), (t, p)) => targetOrReplacement(w, t, p) }.mkString(s"${c.sym}(", ", ", ")")
    }
    cuts.foreach { case w @ Wire(c1, _, c2, _) =>
      assert(c1.ptarget == w)
      assert(c2.ptarget == w)
      if(c1.symId == -1)
        println(s"    ${c1.sym} . ${show(c2)}")
      else if(c2.symId == -1)
        println(s"    ${c2.sym} . ${show(c1)}")
      else {
        println(s"    ${explicit(w)} . ${show(c1)}")
        println(s"    ${explicit(w)} . ${show(c2)}")
      }
    }
  }
}

final case class ProtoCell(sym: Symbol, symId: Int, arity: Int)

final class RuleImpl(cr: CheckedRule, val protoCells: Array[ProtoCell], val freeWires: Array[Int], val freePorts: Array[Int], val connections: Array[Int], val ruleImpls: Array[RuleImpl]) {
  def log(): Unit = {
    println("  Proto cells:")
    protoCells.foreach(pc => println(s"  - $pc"))
    println("  Free wires:")
    freeWires.zip(freePorts).foreach { case (w, p) => println(s"  - ($w, $p)") }
    println("  Connections:")
    connections.grouped(4).zip(ruleImpls).foreach { case (c, ri) => println(s"  - ${c.mkString(",")}: $ri")}
  }
  override def toString = cr.show
}

class Interpreter(globals: Symbols, rules: Iterable[CheckedRule]) extends Scope with BaseInterpreter { self =>

  private[this] val symIds = mutable.HashMap.from[Symbol, Int](globals.symbols.zipWithIndex)
  private[this] val symCount = symIds.size

  override def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, -1)

  private[this] val ruleImpls = new Array[RuleImpl](symCount * symCount)
  private[this] val maxRuleCells = createRuleImpls()
  private[this] val tempCells = new Array[Cell](maxRuleCells)

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
    ris.foreach { ri =>
      ri.connections.grouped(4).zipWithIndex.foreach { case (Array(t1, p1, t2, p2), i) =>
        val pc = ri.protoCells(t1)
        val pc2 = ri.protoCells(t2)
        if(p1 == 0 && p2 == 0 && pc.symId != -1 && pc2.symId != -1) {
          val ri2 = ruleImpls(mkRuleKey(pc.symId, pc2.symId))
          if(ri2 != null) ri.ruleImpls(i) = ri2
        }
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
    val cells = sc.reachableCells.filter(_.symId != -1).toArray
    //println("cells: "+cells.mkString("; "))
    val freeLookup = sc.freeWires.iterator.map { w => (w.sym, w) }.toMap
    //println("freeLookup: "+freeLookup.mkString("; "))
    val wires = (args1 ++ args2).map { i => freeLookup(syms(i)) }.toArray
    //println("wires: "+wires.mkString("; "))
    val lookup = (cells.iterator.zipWithIndex ++ wires.iterator.zipWithIndex.map { case (w, p) => (w, -p-1) }).toMap
    val protoCells = cells.map { c => new ProtoCell(c.sym, getSymbolId(c.sym), c.arity) }
    val conns = mutable.HashSet.empty[Seq[Int]]
    cells.iterator.zipWithIndex.foreach { case (c, i) =>
      c.allCells.zipWithIndex.foreach { case ((_, (t, p)), j) =>
        val w = lookup(t)
        if(w >= 0) {
          if(!conns.contains(Seq(w, p, i, j)))
            conns.add(Seq(i, j, w, p))
        }
      }
    }
    val freeWires = wires.map { w =>
      //println(s"looking up $w: ${w.getCell(0)._1}")
      lookup(w.getCell(0)._1)
    }
    val freePorts = wires.map(_.getCell(0)._2)
    //wires.map(_.sym).zip(freeWires).zip(freePorts).map { case ((s, t), p) => s"$s: ($t, $p)" }.foreach(println)
    new RuleImpl(cr, protoCells, freeWires, freePorts, conns.iterator.flatten.toArray, new Array(conns.size))
  }

  private[this] val cuts = ArrayBuffer.empty[Wire]
  private[this] var nextCut: Wire = null

  @inline def mkRuleKey(w: Wire): Int =
    mkRuleKey(w.leftCell.symId, w.rightCell.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) s1 * symCount + s2 else s2 * symCount + s1

  def reduce(cut: Wire, cells: Array[Cell]): Unit = {
    //TODO: Detect cuts *after* connecting everything
    val ri = cut.ruleImpl
    val (c1, c2) = if(cut.leftCell.symId <= cut.rightCell.symId) (cut.leftCell, cut.rightCell) else (cut.rightCell, cut.leftCell)
    var i = 0
    while(i < ri.protoCells.length) {
      val pc = ri.protoCells(i)
      val c = new Cell(pc.sym, pc.symId, pc.arity)
      cells(i) = c
      i += 1
    }
    i = 0
    val conns = ri.connections
    while(i < conns.length) {
      val t1 = cells(conns(i))
      val p1 = conns(i+1)
      val t2 = cells(conns(i+2))
      val p2 = conns(i+3)
      val ri2 = ri.ruleImpls(i/4)
      i += 4
      val w = new Wire
      connect(t1, p1, w, 0)
      connect(t2, p2, w, 1)
      if(ri2 != null) {
        w.ruleImpl = ri2
        if(nextCut == null) nextCut = w
        else cuts.addOne(w)
      }
    }
    i = 0
    @inline def cutTarget(i: Int) =
      if(i < c1.arity) (c1.auxTargets(i), c1.auxPorts(i)) else (c2.auxTargets(i-c1.arity), c2.auxPorts(i-c1.arity))
    def maybeCreateCut(t: Wire): Unit = {
      if(t.ruleImpl == null) {
        val ri = ruleImpls(mkRuleKey(t))
        if(ri != null) {
          t.ruleImpl = ri
          if(nextCut == null) nextCut = t
          else cuts.addOne(t)
        }
      }
    }
    while(i < ri.freeWires.length) {
      val fw = ri.freeWires(i)
      val (t, p) = cutTarget(i)
      if(fw >= 0) {
        //println(s"Connecting freeWire($i): $t, $p, $fw")
        val (wt, wp) = (cells(fw), ri.freePorts(i))
        connect(wt, wp, t, p)
        val tc = t.getCell(1-p)
        if(tc._2 == 0 && wp == 0 && tc._1.symId != -1 && wt.symId != -1)
          maybeCreateCut(t)
      } else {
        //TODO: Don't remove wires
        val (w2, p2) = cutTarget(-1-fw)
        val (wt, wp) = w2.getCell(1-p2)
        if(i < -1-fw) {
          //println(s"Connecting freeWire($i): $t, $p, $fw")
          connect(wt, wp, t, p)
          val tc = t.getCell(1-p)
          if(tc._2 == 0 && wp == 0 && tc._1.symId != -1 && wt.symId != -1)
            maybeCreateCut(t)
        }
      }
      i += 1
    }
    //cells.take(ri.protoCells.length).foreach { c => println(s"created $c") }
    //cells.take(ri.protoCells.length).foreach { c =>
    //  assert(c.ptarget != null)
    //  c.auxTargets.foreach { w => assert(w != null) }
    //}
  }

  def reduce(): Int = {
    validate()
    var steps = 0
    cuts.clear()
    reachableCells.foreach { c =>
      val w = c.ptarget
      if(w.ruleImpl == null && w.leftPort == 0 && w.rightPort == 0 && w.leftCell.symId != -1 && w.rightCell.symId != -1) {
        val ri = ruleImpls(mkRuleKey(w))
        if(ri != null) {
          w.ruleImpl = ri
          cuts.addOne(w)
        }
      }
    }
    while(!cuts.isEmpty) {
      nextCut = cuts.last
      cuts.dropRightInPlace(1)
      while(nextCut != null) {
        //println(s"Remaining reducible cuts: ${cuts.size+1}")
        steps += 1
        val c = nextCut
        //println(s"Reducing $c with ${c.ruleImpl}")
        //c.ruleImpl.log()
        nextCut = null
        reduce(c, tempCells)
        //validate()
        //println("After reduction:")
        //log()
      }
    }
    //println(steps)
    steps
  }
}
