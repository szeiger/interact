package de.szeiger.interact

import java.io.PrintStream
import scala.annotation.tailrec
import scala.collection.mutable

abstract class Scope[Cell] { self =>
  val freeWires = mutable.HashSet.empty[Cell]

  def createCell(sym: Symbol): Cell
  def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit

  def clear(): Unit = freeWires.clear()

  def add(cuts: Iterable[AST.Cut], syms: Symbols): Unit = {
    class TempWire { var c: Cell = _; var p: Int = 0 }
    @tailrec def connectAny(t1: Any, p1: Int, t2: Any): Unit = (t1, t2) match {
      case (t1: TempWire, t2: Cell @unchecked) => connectAny(t2, -1, t1)
      case (t1: Cell @unchecked, t2: TempWire) if t2.c == null => t2.c = t1; t2.p = p1
      case (t1: Cell @unchecked, t2: TempWire) => connectCells(t1, p1, t2.c, t2.p)
      case (t1: Cell @unchecked, t2: Cell @unchecked) => connectCells(t1, p1, t2, -1)
    }
    def addSyms(e: AST.Expr): Unit = e.allIdents.foreach { i =>
      val s = syms.getOrAdd(i.s)
      if(!s.isCons) s.refs += 1
    }
    cuts.foreach { case AST.Cut(e1, e2) => addSyms(e1); addSyms(e2) }
    val bind = mutable.HashMap.empty[Symbol, TempWire]
    def create(e: AST.Expr): Any = e match {
      case i: AST.Ident =>
        val s = syms.getOrAdd(i.s)
        s.refs match {
          case 0 => createCell(s)
          case 1 => val c = createCell(s); freeWires.addOne(c); c
          case 2 => bind.getOrElseUpdate(s, new TempWire)
          case _ => sys.error(s"Non-linear use of ${i.show} in data")
        }
      case AST.Ap(i, args) =>
        val s = syms.getOrAdd(i.s)
        assert(s.isCons)
        val c = createCell(s)
        args.zipWithIndex.foreach { case (a, p) => connectAny(c, p, create(a)) }
        c
    }
    cuts.foreach(e => connectAny(create(e.left), -1, create(e.right)))
  }
}

abstract class Analyzer[Cell] extends Scope[Cell] { self =>
  def getSymbol(c: Cell): Symbol
  def getConnected(c: Cell, port: Int): (Cell, Int)
  def isFreeWire(c: Cell): Boolean

  def symbolName(c: Cell): String = getSymbol(c).id
  def getArity(c: Cell): Int = getSymbol(c).arity
  def getAllConnected(c: Cell): Iterator[(Cell, Int)] = (-1 until getArity(c)).iterator.map(getConnected(c, _))

  def validate(): Unit =
    reachableCells.flatMap { c1 => getAllConnected(c1).zipWithIndex.map(t => (c1, t)) }.foreach { case (c1, ((c2, p2), p1)) =>
      assert(getConnected(c2, p2) == (c1, p1-1))
    }

  object Church {
    def unapply(c: Cell): Option[Int] = unapply(c, 0)
    @tailrec private[this] def unapply(c: Cell, acc: Int): Option[Int] = (symbolName(c), getArity(c)) match {
      case ("Z", 0) => Some(acc)
      case ("S", 1) =>
        val (c2, p2) = getConnected(c, 0)
        if(p2 != -1) None else unapply(c2, acc+1)
      case _ => None
    }
  }

  object ListCons {
    def unapply(c: Cell): Option[(Cell, Cell)] = (symbolName(c), getArity(c)) match {
      case ("Cons", 2) =>
        val (c1, p1) = getConnected(c, 0)
        val (c2, p2) = getConnected(c, 1)
        if(p1 < 0 && p2 < 0) Some((c1, c2)) else None
      case _ => None
    }
  }

  def reachableCells: Iterator[Cell] = {
    val s = mutable.HashSet.empty[Cell]
    val q = mutable.ArrayBuffer.from(freeWires.flatMap(getAllConnected(_).map(_._1)))
    while(q.nonEmpty) {
      val w = q.last
      q.dropRightInPlace(1)
      if(s.add(w)) q.addAll(getAllConnected(w).map(_._1))
    }
    s.iterator
  }

  def getCutLogs: Iterator[(Cell, String, String, Option[String])] = {
    class Wire(val c1: Cell, val p1: Int, val c2: Cell, val p2: Int) {
      override def hashCode(): Int = (c1, p1).hashCode() + (c2, p2).hashCode()
      override def equals(obj: Any): Boolean = obj match {
        case w: Wire =>
          (c1 == w.c1 && p1 == w.p1 && c2 == w.c2 && p2 == w.p2) || (c1 == w.c2 && p1 == w.p2 && c2 == w.c1 && p2 == w.p1)
        case _ => false
      }
    }
    val wires = mutable.HashMap.empty[Wire, Wire]
    def wire(c1: Cell, p1: Int): Wire = {
      val (c2, p2) = getConnected(c1, p1)
      val w1 = new Wire(c1, p1, c2, p2)
      wires.getOrElseUpdate(w1, w1)
    }
    val cuts = mutable.HashSet.from(reachableCells.filter(c => getConnected(c, -1)._2 == -1)).map(c => wire(c, -1))
    var nextTemp = -1
    val helpers = mutable.Map.empty[Wire, String]
    def explicit(w: Wire): String = helpers.getOrElseUpdate(w, {
      nextTemp += 1
      "$" + nextTemp
    })
    def targetOrReplacement(t: Cell, p: Int): String = {
      val w = wire(t, p)
      if(freeWires.contains(t)) symbolName(t)
      else helpers.get(w) match {
        case Some(s) => s
        case None if p == -1 => show(t)
        case None => explicit(w)
      }
    }
    def show(c: Cell): String = c match {
      case Church(i) => s"$i'c"
      case ListCons(c1, c2) => s"${show(c1)} :: ${show(c2)}"
      case c if getArity(c) == 0 => symbolName(c)
      case c => getAllConnected(c).drop(1).map { case (t, p) => targetOrReplacement(t, p) }.mkString(s"${symbolName(c)}(", ", ", ")")
    }
    val strs = cuts.iterator.map { w =>
      val c1 = w.c1
      val c2 = w.c2
      if(isFreeWire(c1)) (c1, symbolName(c1), show(c2), None)
      else if(isFreeWire(c2)) (c1, symbolName(c2), show(c1), None)
      else (c1, explicit(w), show(c1), Some(show(c2)))
    }
    val freeWireNames = freeWires.map(symbolName)
    strs.zipWithIndex.toIndexedSeq.sortBy { case ((_, l, _, _), idx) =>
      val f = freeWireNames.contains(l)
      (!f, if(f) l else "", idx)
    }.iterator.map(_._1)
  }

  def log(out: PrintStream): Unit = getCutLogs.foreach { case (_, l, r, o) =>
    out.println(s"  $l . $r")
    o.foreach(r2 => out.println(s"  $l . $r2"))
  }
}
