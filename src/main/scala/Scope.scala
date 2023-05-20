package de.szeiger.interact

import java.io.PrintStream
import scala.annotation.tailrec
import scala.collection.mutable

abstract class Scope[Cell >: Null <: AnyRef] { self =>
  val freeWires = mutable.HashSet.empty[Cell]

  def createCell(sym: Symbol): Cell
  def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit
  def getSymbol(c: Cell): Symbol
  def getArity(c: Cell): Int
  def getConnected(c: Cell, port: Int): (Cell, Int)
  def isFreeWire(c: Cell): Boolean

  class Delegate extends Scope[Cell] {
    def createCell(sym: Symbol): Cell = self.createCell(sym)
    def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit = self.connectCells(c1, p1, c2, p2)
    def getSymbol(c: Cell): Symbol = self.getSymbol(c)
    def getArity(c: Cell): Int = self.getArity(c)
    def getConnected(c: Cell, port: Int): (Cell, Int) = self.getConnected(c, port)
    def isFreeWire(c: Cell): Boolean = self.isFreeWire(c)
  }

  def symbolName(c: Cell): String = getSymbol(c).id.s
  def getAllConnected(c: Cell): Iterator[(Cell, Int)] = (-1 until getArity(c)).iterator.map(getConnected(c, _))

  private def addSymbols(cs: Iterable[AST.Cut], symbols: Symbols): Unit = {
    def f(e: AST.Expr): Unit = e match {
      case i: AST.Ident =>
        val s = symbols.getOrAdd(i)
        if(!s.isCons) s.refs += 1
      case AST.Ap(i, es) => f(i); es.foreach(f)
    }
    cs.foreach { c => f(c.left); f(c.right) }
  }

  def clear(): Unit = freeWires.clear()

  def add(cuts: Iterable[AST.Cut], syms: Symbols): Unit = {
    class TempWire { var c: Cell = _; var p: Int = 0 }
    @tailrec
    def connectAny(t1: AnyRef, p1: Int, t2: AnyRef, p2: Int): Unit = {
      (t1, t2) match {
        case (t1: TempWire, t2: Cell) =>
          connectAny(t2, p2, t1, p1)
        case (t1: Cell, t2: TempWire) =>
          if(t2.c == null) { t2.c = t1; t2.p = p1 }
          else connectCells(t1, p1, t2.c, t2.p)
        case (t1: Cell, t2: Cell) =>
          connectCells(t1, p1, t2, p2)
      }
    }
    addSymbols(cuts, syms)
    val bind = mutable.HashMap.empty[Symbol, TempWire]
    val toCreate = mutable.Queue.empty[(AST.Expr, Cell, Int)]
    def create(e: AST.Expr, cCell: Cell, cPort: Int): (AnyRef, Int) = {
      val (wr: AnyRef, pr: Int) = e match {
        case i: AST.Ident =>
          val s = syms.getOrAdd(i)
          if(s.isCons) {
            val s = syms.getOrAdd(i)
            val c = createCell(s)
            (c, -1)
          } else if(s.refs == 1) {
            val c = createCell(s)
            freeWires.addOne(c)
            (c, -1)
          } else if(s.refs == 2) {
            bind.get(s) match {
              case Some(w) => (w, 0)
              case None =>
                val w = new TempWire
                bind.put(s, w)
                (w, -1)
            }
          } else sys.error(s"Non-linear use of ${i.show} in data")
        case AST.Ap(i, args) =>
          val s = syms.getOrAdd(i)
          assert(s.isCons)
          val c = createCell(s)
          args.zipWithIndex.foreach { case (a, p) => toCreate.enqueue((a, c, p)) }
          (c, -1)
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
      while(toCreate.nonEmpty) {
        val (e, c, p) = toCreate.dequeue()
        create(e, c, p)
      }
    }
  }

  def validate(): Unit = {
    reachableCells.flatMap { c1 => getAllConnected(c1).zipWithIndex.map(t => (c1, t)) }.foreach { case (c1, ((c2, p2), p1)) =>
      assert(getConnected(c2, p2) == (c1, p1-1))
    }
  }

  object Church {
    def unapply(_c: Cell): Option[Int] = {
      var acc = 0
      var c = _c
      while(true) {
        if(symbolName(c) == "Z" && getArity(c) == 0) return Some(acc)
        else if(symbolName(c) == "S" && getArity(c) == 1) {
          getConnected(c, 0) match {
            case (c2, -1) => c = c2; acc += 1
            case _ => return None
          }
        } else return None
      }
      None
    }
  }

  object ListCons {
    def unapply(c: Cell): Option[(Cell, Cell)] = {
      if(symbolName(c) == "Cons" && getArity(c) == 2) {
        val (c1, p1) = getConnected(c, 0)
        val (c2, p2) = getConnected(c, 1)
        if(p1 < 0 && p2 < 0) Some((c1, c2)) else None
      } else None
    }
  }

  def reachableCells: Iterator[Cell] = {
    val s = mutable.HashSet.empty[Cell]
    val q = mutable.Queue.from(freeWires.flatMap(c => getAllConnected(c).map(_._1)))
    while(q.nonEmpty) {
      val w = q.dequeue()
      if(s.add(w)) q.enqueueAll(getAllConnected(w).map(_._1))
    }
    s.iterator
  }

  def getCutLogs: Iterator[(Cell, String, String, Option[String])] = {
    val freeWireNames = freeWires.map(symbolName)
    val leaders = mutable.HashMap.empty[Cell, Cell]
    def leader(w: Cell): Cell = leaders.getOrElse(w, leaders.getOrElseUpdate(getConnected(w, -1)._1, w))
    val cuts = mutable.HashSet.from(reachableCells.filter(c => getConnected(c, -1)._2 == -1)).map(leader)
    var nextTemp = -1
    val helpers = mutable.Map.empty[Cell, String]
    def explicit(ldr: Cell): String = helpers.getOrElseUpdate(ldr, {
      nextTemp += 1
      "$" + nextTemp
    })
    def targetOrReplacement(t: Cell, p: Int): String = {
      val ldr = leader(t)
      helpers.get(ldr) match {
        case Some(s) => s
        case None if p == -1 => show(t)
        case None => explicit(ldr)
      }
    }
    def show(c: Cell): String = c match {
      case Church(i) => s"$i'c"
      case ListCons(c1, c2) => s"${show(c1)} :: ${show(c2)}"
      case c if getArity(c) == 0 => symbolName(c)
      case c => getAllConnected(c).drop(1).map { case (t, p) => targetOrReplacement(t, p) }.mkString(s"${symbolName(c)}(", ", ", ")")
    }
    val strs = cuts.iterator.map { w =>
      val c1 = leader(w)
      val c2 = getConnected(c1, -1)._1
      if(isFreeWire(c1)) (c1, symbolName(c1), show(c2), None)
      else if(isFreeWire(c2)) (c1, symbolName(c2), show(c1), None)
      else (c1, explicit(w), show(c1), Some(show(c2)))
    }
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
