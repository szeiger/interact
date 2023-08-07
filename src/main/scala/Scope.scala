package de.szeiger.interact

import java.io.PrintStream
import scala.annotation.tailrec
import scala.collection.mutable

import de.szeiger.interact.ast._

abstract class Scope[Cell] { self =>
  val freeWires = mutable.HashSet.empty[Cell]

  def createCell(sym: Symbol, payload: Option[EmbeddedExpr]): Cell
  def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit

  def clear(): Unit = freeWires.clear()

  def addData(data: Let): Unit = {
    val createEmb = mutable.ArrayBuffer.empty[(Symbol, EmbeddedExpr, Cell)]
    val catchEmb: Scope[Cell] = new Scope[Cell] {
      override def createCell(sym: Symbol, payload: Option[EmbeddedExpr]): Cell = {
        val c = self.createCell(sym, None)
        payload.foreach(emb => createEmb += ((sym, emb, c)))
        c
      }
      override def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit = self.connectCells(c1, p1, c2, p2)
    }
    catchEmb.addExprs(data.defs)
    freeWires ++= catchEmb.freeWires
    val foundEmbIds = mutable.HashMap.empty[String, Cell]
    createEmb.foreach { case (sym, e, c) =>
      e match {
        case IntLit(v) =>
          assert(sym.payloadType == PayloadType.INT)
          c.asInstanceOf[IntBox].setValue(v)
        case StringLit(v) =>
          assert(sym.payloadType == PayloadType.REF)
          c.asInstanceOf[RefBox].setValue(v)
        case Ident(id) =>
          if(foundEmbIds.put(id, c).isDefined)
            sys.error(s"Invalid payload expression ${e.show} in ${data.show}: Duplicate use of variable")
        case _ => sys.error(s"Invalid payload expression ${e.show} in data ${data.show}")
      }
    }
    val embComp = data.embDefs.map { ee =>
      val as = mutable.HashMap.empty[String, Int]
      val ec = EmbeddedComputation.apply(getClass.getClassLoader, ee)(data.show) { a =>
        as.put(a, as.getOrElse(a, 0) + 1)
        foundEmbIds.remove(a) match {
          case Some(s) => s
          case None => sys.error(s"Non-linear variable use in embedded method call ${ee.show} in data ${data.show}")
        }
      }
      if(as.exists(_._2 != 1))
        sys.error(s"Non-linear variable use in embedded method call ${ee.show} in data ${data.show}")
      ec
    }
    if(foundEmbIds.nonEmpty) sys.error(s"Non-linear variable use of ${foundEmbIds.mkString(", ")} in data ${data.show}")
    embComp.foreach { e => e.invoke(e.argIndices) }
  }

  def addExprs(defs: Iterable[Expr]): Unit = {
    class TempWire { var c: Cell = _; var p: Int = 0 }
    @tailrec def connectAny(t1: Any, p1: Int, t2: Any, p2: Int): Unit = (t1, t2) match {
      case (t1: TempWire, t2: Cell @unchecked) => connectAny(t2, p2, t1, p1)
      case (t1: Cell @unchecked, t2: TempWire) if t2.c == null => t2.c = t1; t2.p = p1
      case (t1: Cell @unchecked, t2: TempWire) => connectCells(t1, p1, t2.c, t2.p)
      case (t1: Cell @unchecked, t2: Cell @unchecked) => connectCells(t1, p1, t2, p2)
    }
    val refs = new RefsMap
    for(e <- defs; i <- e.allIdents) {
      val s = i.sym
      assert(s.isDefined)
      if(!s.isCons) refs.inc(s)
    }
    def cellRet(s: Symbol, c: Cell): Seq[(Any, Int)] = {
      if(s.isDef) (s.arity-s.returnArity).until(s.arity).map(p => (c, p))
      else Seq((c, -1))
    }
    val bind = mutable.HashMap.empty[Symbol, TempWire]
    def create(e: Expr): Seq[(Any, Int)] = e match {
      case i: Ident =>
        val s = i.sym
        assert(s.isDefined)
        refs(s) match {
          case 0 => cellRet(s, createCell(s, None))
          case 1 => val c = createCell(s, None); freeWires.addOne(c); cellRet(s, c)
          case 2 => Seq((bind.getOrElseUpdate(s, new TempWire), -1))
          case _ => sys.error(s"Non-linear use of ${i.show} in data")
        }
      case Tuple(es) => es.flatMap(create)
      case Apply(i, emb, args) =>
        val s = i.sym
        assert(s.isCons)
        val c = createCell(s, emb)
        args.zipWithIndex.foreach { case (a, p0) =>
          val p = if(!s.isDef) p0 else p0-1
          val ca = create(a)
          assert(ca.length == 1)
          connectAny(c, p, ca.head._1, ca.head._2)
        }
        cellRet(s, c)
    }
    defs.foreach {
      case Assignment(e1, e2) =>
        val c1 = create(e1)
        val c2 = create(e2)
        assert(c1.length == c2.length)
        c1.zip(c2).foreach { case ((t1, p1), (t2, p2)) => connectAny(t1, p1, t2, p2) }
      case e: Apply =>
        val c = create(e)
        assert(c.isEmpty)
    }
  }
}

abstract class Analyzer[Cell] extends Scope[Cell] { self =>
  def getSymbol(c: Cell): Symbol
  def getConnected(c: Cell, port: Int): (Cell, Int)
  def isFreeWire(c: Cell): Boolean
  def getPayload(c: Cell): Any

  def symbolName(c: Cell): String = getSymbol(c).id
  def getArity(c: Cell): Int = getSymbol(c).arity
  def getAllConnected(c: Cell): Iterator[(Cell, Int)] = (-1 until getArity(c)).iterator.map(getConnected(c, _))

  def validate(): Unit =
    reachableCells.flatMap { c1 => getAllConnected(c1).zipWithIndex.map(t => (c1, t)) }.foreach { case (c1, ((c2, p2), p1)) =>
      assert(getConnected(c2, p2) == (c1, p1-1))
    }

  object Nat {
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

  def log(out: PrintStream, prefix: String = "  ", markCut: (Cell, Cell) => Boolean = (_, _) => false, color: Boolean = true): mutable.ArrayBuffer[Cell] = {
    val colors = if(color) MaybeColors else NoColors
    import colors._
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
    def show(c1: Cell, withRet: Boolean): String = {
      shown += c1
      val sym = getSymbol(c1)
      def list(poss: IndexedSeq[Int]) = poss.map { p1 => val (c2, p2) = getConnected(c1, p1); (getSymbol(c2), nameOrSubst(c1, p1, c2, p2)) }
      def needsParens(thisSym: Symbol, thisPre: Int, nestedSym: Symbol): Boolean = {
        val nestedPre = Lexical.precedenceOf(nestedSym.id)
        nestedPre > thisPre || (nestedPre >= 0 && (Lexical.isRightAssoc(thisSym.id) != Lexical.isRightAssoc(nestedSym.id)))
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
            val as1 = as0.map { case (asym, s) => if(needsParens(sym, pr1, asym)) s"($s)" else s }
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
    cuts
  }
}

trait BaseInterpreter {
  def scope: Analyzer[_]
  def reduce(): Int
}
