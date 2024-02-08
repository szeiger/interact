package de.szeiger.interact

import java.io.PrintStream
import scala.annotation.tailrec
import scala.collection.mutable
import de.szeiger.interact.ast._

trait Analyzer[Cell] { self =>
  def rootCells: IterableOnce[Cell]
  def irreduciblePairs: IterableOnce[(Cell, Cell)]

  def getSymbol(c: Cell): Symbol
  def getConnected(c: Cell, port: Int): (Cell, Int)
  def isFreeWire(c: Cell): Boolean
  def isSharedSingleton(c: Cell): Boolean
  def getPayload(c: Cell): Any

  def symbolName(c: Cell): String = getSymbol(c).id
  def getArity(c: Cell): Int = getSymbol(c).arity

  private[this] def getAllConnected(c: Cell): Iterator[(Cell, Int)] =
    if(isFreeWire(c)) Iterator(getConnected(c, 0))
    else (-1 until getArity(c)).iterator.map(getConnected(c, _))

  private[this] object Nat {
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
    val freeWires = rootCells.iterator.filter(isFreeWire).toVector
    val s = mutable.HashSet.empty[Cell]
    val q = mutable.ArrayBuffer.from(freeWires.flatMap(getAllConnected(_).filter(_ != null).map(_._1)))
    while(q.nonEmpty) {
      val w = q.last
      q.dropRightInPlace(1)
      if(s.add(w)) q.addAll(getAllConnected(w).map(_._1))
    }
    s.iterator
  }

  private[this] def allConnections(): (mutable.HashMap[(Cell, Int), (Cell, Int)], mutable.HashSet[Cell]) = {
    val m = mutable.HashMap.empty[(Cell, Int), (Cell, Int)]
    val s = mutable.HashSet.empty[Cell]
    val q = mutable.ArrayBuffer.from(rootCells)
    while(q.nonEmpty) {
      val c1 = q.last
      q.dropRightInPlace(1)
      if(s.add(c1)) {
        val isWire = isFreeWire(c1)
        val conn = getAllConnected(c1).toVector
        conn.zipWithIndex.foreach {
          case (null, _) =>
          case ((c2, p2), _p1) =>
            val p1 = if(isWire) 0 else _p1 - 1
            m.put((c1, p1), (c2, p2))
            m.put((c2, p2), (c1, p1))
        }
        q.addAll(conn.iterator.filter(_ != null).map(_._1))
      }
    }
    (m, s)
  }

  def log(out: PrintStream, prefix: String = "  ", markCut: (Cell, Cell) => Boolean = (_, _) => false, color: Boolean = true): mutable.ArrayBuffer[(Cell, Cell)] = {
    val colors = if(color) MaybeColors else NoColors
    import colors._
    val cuts = mutable.ArrayBuffer.empty[(Cell, Cell)]
    def singleRet(s: Symbol): Int = if(!s.isDef) -1 else if(s.returnArity == 1) s.callArity-1 else -2
    val freeWires = rootCells.iterator.filter(isFreeWire).toVector
    val stack = mutable.Stack.from(freeWires.sortBy(c => symbolName(c)))
    val all = allConnections()._1
    val shown = mutable.HashSet.empty[Cell]
    var lastTmp = 0
    def tmp(): String = { lastTmp += 1; s"$$s$lastTmp" }
    val subst = mutable.HashMap.from(freeWires.iterator.map(c1 => ((c1, 0), symbolName(c1))))
    //println(s"**** $subst")
    //def id(c: Cell): String = if(c == null) "null" else s"${getSymbol(c)}#${System.identityHashCode(c)}"
    //all.foreach { case ((c1, p1), (c2, p2)) => println(s"    ${id(c1)}:$p1 . ${id(c2)}:$p2") }
    def nameOrSubst(c1: Cell, p1: Int, c2: Cell, p2: Int): String = subst.get(c2, p2) match {
      case Some(s) => s
      case None =>
        val mark = if(p1 == -1 && p2 == -1 && markCut(c1, c2)) {
          cuts.addOne((c1, c2))
          s"${cBlue}<${cuts.length-1}>${cNormal}"
        } else ""
        if(singleRet(getSymbol(c2)) == p2) mark + show(c2, false)
        else {
          if(!shown.contains(c2)) stack += c2
          val t = tmp()
          subst.put((c1, p1), t)
          mark + t
        }
    }
    def show(_c1: Cell, withRet: Boolean): String = {
      val c1 = if(isFreeWire(_c1)) getConnected(_c1, 0)._1 else _c1
      shown += c1
      val sym = getSymbol(c1)
      def list(poss: IndexedSeq[Int]) = poss.map { p1 =>
        if(p1 == -1 && isFreeWire(_c1)) (getSymbol(_c1), nameOrSubst(c1, p1, _c1, 0))
        else all.get(c1, p1) match {
          case Some((c2, p2)) => (getSymbol(c2), nameOrSubst(c1, p1, c2, p2))
          case None => (Symbol.NoSymbol, "?")
        }
      }
      def needsParens(sym1: Symbol, pre1: Int, sym2: Symbol, sym2IsRight: Boolean): Boolean = {
        val pre2 = Lexical.precedenceOf(sym2.id)
        val r1 = Lexical.isRightAssoc(sym1.id)
        val r2 = Lexical.isRightAssoc(sym2.id)
        pre2 > pre1 || (pre2 >= 0 && (r1 != r2)) || (pre1 == pre2 && r1 != sym2IsRight && r2 != sym2IsRight)
      }
      val call = c1 match {
        case Nat(v) => s"${v}n"
        case _ =>
          val aposs = if(sym.isDef) -1 +: (0 until sym.callArity-1) else 0 until sym.arity
          val as0 = list(aposs)
          val pr1 = Lexical.precedenceOf(sym.id)
          val nameAndValue = sym.payloadType match {
            case PayloadType.VOID => s"$cYellow${sym.id}$cNormal"
            case _ =>
              val s = getPayload(c1) match {
                case s: String => s"\"$s\""
                case o => String.valueOf(o)
              }
              s"$cYellow${sym.id}$cNormal[$s]"
          }
          if(pr1 >= 0 && sym.arity == 2) {
            val as1 = as0.zipWithIndex.map { case ((asym, s), idx) => if(needsParens(sym, pr1, asym, idx == 1)) s"($s)" else s }
            s"${as1(0)} $nameAndValue ${as1(1)}"
          } else {
            val as = if(as0.isEmpty) "" else as0.iterator.map(_._2).mkString("(", ", ", ")")
            s"$nameAndValue$as"
          }
      }
      if(withRet) {
        val rposs = if(sym.isDef) sym.callArity-1 until sym.callArity+sym.returnArity-1 else IndexedSeq(-1)
        val rs0 = list(rposs).map(_._2)
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
    val irr = irreduciblePairs.iterator.filter { case (c1, c2) => c1 != null && c2 != null }.map { case (c1, c2) => Seq(symbolName(c1), symbolName(c2)).sorted.mkString(" <-> ") }.toVector.sorted
    if(irr.nonEmpty) {
      out.println()
      out.println("Irreducible pairs:")
      irr.foreach(s => out.println(s"  $s"))
    }
    cuts
  }

  def toDot(out: PrintStream): Unit = {
    var lastIdx = 0
    def mk(): String = { lastIdx += 1; s"n$lastIdx" }
    val cells = allConnections()._2.map(c => (c, mk())).toMap
    out.println("graph G {")
    out.println("  node [shape=plain];")
    cells.foreachEntry { (c, l) =>
      val sym = getSymbol(c)
      if(sym.arity == 0)
        out.println(
          s"""  $l [shape=circle label=<${sym.id}>];""".stripMargin
        )
      else {
        val ports = (sym.arity to 1 by -1).map(i => s"""<td port="$i"></td>""").mkString
        out.println(
          s"""  $l [shape=plain label=<<table border="0" cellborder="1" cellspacing="0">
             |      <tr><td border="0"></td><td port="0"></td><td border="0"></td></tr>
             |      <tr><td colspan="3">${sym.id}</td></tr>
             |      <tr><td colspan="3" cellpadding="0" border="0"><table border="0" cellspacing="0" cellborder="1"><tr>$ports</tr></table></td></tr>
             |    </table>>];""".stripMargin
        )
      }
    }
    val done = mutable.HashSet.empty[(Cell, Int)]
    cells.foreachEntry { (c1, l1) =>
      getAllConnected(c1).zipWithIndex.foreach { case ((c2, _p2), p1) =>
        if(!done.contains((c1, p1))) {
          val p2 = _p2 + 1
          val l2 = cells(c2)
          val st =
            if(p1 == 0 && p2 == 0) " [style=bold]"
            else if(p1 != 0 && p2 != 0) " [style=dashed]"
            else ""
          out.println(s"""  $l1:$p1 -- $l2:$p2$st;""")
          done += ((c2, p2))
        }
      }
    }
    out.println("}")
  }
}
