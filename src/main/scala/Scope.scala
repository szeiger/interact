package de.szeiger.interact

import java.io.PrintStream
import scala.annotation.tailrec
import scala.collection.mutable

abstract class Scope[Cell] { self =>
  val freeWires = mutable.HashSet.empty[Cell]

  def createCell(sym: Symbol): Cell
  def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit

  def clear(): Unit = freeWires.clear()

  def addExprs(defs: Iterable[AST.Expr], syms: Symbols): Unit = {
    class TempWire { var c: Cell = _; var p: Int = 0 }
    @tailrec def connectAny(t1: Any, p1: Int, t2: Any, p2: Int): Unit = (t1, t2) match {
      case (t1: TempWire, t2: Cell @unchecked) => connectAny(t2, p2, t1, p1)
      case (t1: Cell @unchecked, t2: TempWire) if t2.c == null => t2.c = t1; t2.p = p1
      case (t1: Cell @unchecked, t2: TempWire) => connectCells(t1, p1, t2.c, t2.p)
      case (t1: Cell @unchecked, t2: Cell @unchecked) => connectCells(t1, p1, t2, p2)
    }
    for(e <- defs; i <- e.allIdents) {
      val s = syms.getOrAdd(i.s)
      if(!s.isCons) s.refs += 1
    }
    def cellRet(s: Symbol, c: Cell): Seq[(Any, Int)] = {
      if(s.isDef) (s.arity-s.returnArity).until(s.arity).map(p => (c, p))
      else Seq((c, -1))
    }
    val bind = mutable.HashMap.empty[Symbol, TempWire]
    def create(e: AST.Expr): Seq[(Any, Int)] = e match {
      case i: AST.Ident =>
        val s = syms.getOrAdd(i.s)
        s.refs match {
          case 0 => cellRet(s, createCell(s))
          case 1 => val c = createCell(s); freeWires.addOne(c); cellRet(s, c)
          case 2 => Seq((bind.getOrElseUpdate(s, new TempWire), -1))
          case _ => sys.error(s"Non-linear use of ${i.show} in data")
        }
      case AST.Tuple(es) => es.flatMap(create)
      case AST.Ap(i, args) =>
        val s = syms.getOrAdd(i.s)
        assert(s.isCons)
        val c = createCell(s)
        args.zipWithIndex.foreach { case (a, p0) =>
          val p =
            if(!s.isDef) p0
            else if(p0 == 0) -1
            else p0-1
          val ca = create(a)
          assert(ca.length == 1)
          connectAny(c, p, ca.head._1, ca.head._2)
        }
        cellRet(s, c)
    }
    defs.foreach {
      case AST.Assignment(e1, e2) =>
        val c1 = create(e1)
        val c2 = create(e2)
        assert(c1.length == c2.length)
        c1.zip(c2).foreach { case ((t1, p1), (t2, p2)) => connectAny(t1, p1, t2, p2) }
      case e: AST.Ap =>
        val c = create(e)
        assert(c.isEmpty)
    }
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

  def log(out: PrintStream, prefix: String = "  ", markCut: (Cell, Cell) => Boolean = (_, _) => false): mutable.ArrayBuffer[Cell] = {
    val cuts = mutable.ArrayBuffer.empty[Cell]
    def singleRet(s: Symbol): Int = if(!s.isDef) -1 else if(s.returnArity == 1) s.callArity-1 else -2
    val stack = mutable.Stack.from(freeWires.toIndexedSeq.sortBy(c => getSymbol(c).id).map(c => getConnected(c, -1)._1))
    val shown = mutable.HashSet.empty[Cell]
    var lastTmp = 0
    def tmp(): String = { lastTmp += 1; s"$$s$lastTmp" }
    val subst = mutable.HashMap.from(freeWires.iterator.map(c1 => ((c1, -1), getSymbol(c1).id)))
    def nameOrSubst(c1: Cell, p1: Int, c2: Cell, p2: Int): String = subst.get(c2, p2) match {
      case Some(s) => s
      case None =>
        val mark = if(p1 == -1 && p2 == -1 && markCut(c1, c2)) {
          cuts.addOne(c1)
          s"<${cuts.length-1}>"
        } else ""
        if(singleRet(getSymbol(c2)) == p2) mark + show(c2, false)
        else {
          if(!shown.contains(c2)) stack += c2
          val t = tmp()
          subst.put((c1, p1), t)
          mark + t
        }
    }
    def show(c1: Cell, withRet: Boolean): String = {
      shown += c1
      val sym = getSymbol(c1)
      def list(poss: IndexedSeq[Int]) = poss.map { p1 => val (c2, p2) = getConnected(c1, p1); (getSymbol(c2), nameOrSubst(c1, p1, c2, p2)) }
      def needsParens(thisSym: Symbol, thisPre: Int, nestedSym: Symbol): Boolean = {
        val nestedPre = Lexical.precedenceOf(nestedSym.id)
        nestedPre > thisPre || (nestedPre >= 0 && (Lexical.isRightAssoc(thisSym.id) != Lexical.isRightAssoc(nestedSym.id)))
      }
      val call = c1 match {
        case Church(v) => s"$v'c"
        case _ =>
          val aposs = if(sym.isDef) -1 +: (0 until sym.callArity-1) else 0 until sym.arity
          val as0 = list(aposs)
          val pr1 = Lexical.precedenceOf(sym.id)
          if(pr1 >= 0 && sym.arity == 2) {
            val as1 = as0.map { case (asym, s) => if(needsParens(sym, pr1, asym)) s"($s)" else s }
            s"${as1(0)} ${sym.id} ${as1(1)}"
          } else {
            val as = if(as0.isEmpty) "" else as0.iterator.map(_._2).mkString("(", ", ", ")")
            s"${sym.id}$as"
          }
      }
      if(withRet) {
        val rposs = if(sym.isDef) sym.callArity-1 until sym.callArity+sym.returnArity-1 else IndexedSeq(-1)
        val rs0 = list(rposs).map(_._1)
        rs0.size match {
          case 0 => call
          case 1 => s"${rs0.head} = $call"
          case _ => rs0.mkString("(", ", ", s") = $call")
        }
      } else call
    }
    while(stack.nonEmpty) {
      val c1 = stack.pop()
      if(!shown.contains(c1)) {
        val s = show(c1, true)
        out.println(s"$prefix$s")
      }
    }
    cuts
  }
}
