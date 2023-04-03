package de.szeiger.interact

import scala.annotation.tailrec
import scala.collection.mutable

class Symbol(val id: AST.Ident) {
  var refs = 0
  var cons: AST.Cons = null
  def isCons = cons != null
  override def toString = id.show
}

class Symbols(parent: Option[Symbols] = None) {
  private val syms = mutable.HashMap.empty[AST.Ident, Symbol]
  def getOrAdd(id: AST.Ident): Symbol = {
    val so = parent match {
      case Some(p) => p.syms.get(id)
      case None => None
    }
    so.getOrElse(syms.getOrElseUpdate(id, new Symbol(id)))
  }
  def get(id: AST.Ident): Option[Symbol] = {
    val so = parent match {
      case Some(p) => p.syms.get(id)
      case None => None
    }
    so.orElse(syms.get(id))
  }
  def apply(id: AST.Ident): Symbol =
    get(id).getOrElse(sys.error(s"No symbol found for ${id.show}"))
}

trait Target {
  var principal: (Target, Int) = _
  def connect(slot: Int, t: Target, tslot: Int): Unit = {
    assert(slot == 0)
    principal = (t, tslot)
  }
  def getPort(slot: Int): (Target, Int) = {
    assert(slot == 0)
    principal
  }
}

final class Wire(val sym: Symbol) extends Target

final class Cell(val sym: Symbol, val arity: Int) extends Target {
  var aux = new Array[(Target, Int)](arity)
  override def connect(slot: Int, t: Target, tslot: Int) = {
    if(slot != 0) aux(slot-1) = (t, tslot)
    else super.connect(slot, t, tslot)
  }
  override def getPort(slot: Int): (Target, Int) = {
    if(slot != 0) aux(slot-1)
    else super.getPort(slot)
  }
}

class Scope {
  val cells = mutable.HashSet.empty[Cell]
  val freeWires = mutable.HashSet.empty[Wire]

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
    addSymbols(cuts, syms)
    val bind = mutable.HashMap.empty[Symbol, Wire]
    def create(e: AST.Expr): (Target, Int) = e match {
      case i: AST.Ident =>
        val s = syms.getOrAdd(i)
        if(s.isCons) {
          val s = syms.getOrAdd(i)
          val c = new Cell(s, s.cons.arity)
          cells.addOne(c)
          (c, 0)
        } else if(s.refs == 1) {
          val w = new Wire(s)
          freeWires.addOne(w)
          (w, 0)
        } else if(s.refs == 2) {
          bind.get(s) match {
            case Some(w) =>
              w.principal
            case None =>
              val w = new Wire(s)
              bind.put(s, w)
              (w, 0)
          }
        } else sys.error(s"Non-linear use of ${i.show} in data")
      case AST.Ap(i, args) =>
        val s = syms.getOrAdd(i)
        assert(s.isCons)
        val c = new Cell(s, s.cons.arity)
        cells.addOne(c)
        args.zipWithIndex.foreach { case (a, idx) =>
          val slot = idx + 1
          val (at, as) = create(a)
          c.connect(slot, at, as)
          at.connect(as, c, slot)
        }
        (c, 0)
    }
    def createCut(e: AST.Cut): Unit = {
      val (lt, ls) = create(e.left)
      val (rt, rs) = create(e.right)
      lt.connect(ls, rt, rs)
      rt.connect(rs, lt, ls)
      null
    }
    cuts.foreach(createCut)
  }

  private def chainStart(c: Cell): Cell = {
    val visited = mutable.HashSet.empty[Cell]
    @tailrec def f(c: Cell): Cell = c.principal match {
      case null => c
      case (p: Cell, ps) if ps != 0 && !visited.contains(p) =>
        visited.addOne(c)
        f(p)
      case _ => c
    }
    f(c)
  }

  object Church {
    def unapply(c: Cell): Option[Int] = {
      if(c.sym.id.s == "Z" && c.arity == 0) Some(0)
      else if(c.sym.id.s == "S" && c.arity == 1) {
        c.getPort(1) match {
          case (c2: Cell, 0) => unapply(c2).map(_ + 1)
          case _ => None
        }
      } else None
    }
  }

  def log(): Unit = {
    println(s"Free wires: ${freeWires.map(_.sym).mkString(", ")}")
    val rem = mutable.HashSet.from(cells)
    val helpers = mutable.HashMap.empty[(Target, Int), String]
    var nextHelper = 0
    def removeChurch(c: Cell): Unit = {
      rem.remove(c)
      if(c.arity > 0) removeChurch(c.getPort(1)._1.asInstanceOf[Cell])
    }
    def targetOrReplacement(t: Target, p: Int): String = {
      if(p == 0) show(t) else {
        helpers.get((t, p)) match {
          case Some(s) => s
          case None =>
            val s = s"$$${nextHelper}"
            nextHelper += 1
            helpers.put(t.getPort(p), s)
            s
        }
      }
    }
    def show(t: Target): String = t match {
      case c @ Church(i) =>
        removeChurch(c)
        s"$i'c"
      case c: Cell =>
        if(!rem.contains(c)) "<error: duplicate>"
        else {
          rem.remove(c)
          if(c.sym.id.s == "Cons" && c.arity == 2 && c.aux(0)._2 == 0 && c.aux(1)._2 == 0) {
            val lhs = targetOrReplacement(c.aux(0)._1, c.aux(0)._2)
            val rhs = targetOrReplacement(c.aux(1)._1, c.aux(1)._2)
            s"$lhs :: $rhs"
          } else if(c.arity == 0) c.sym.toString
          else c.aux.map { case (t, p) => targetOrReplacement(t, p) }.mkString(s"${c.sym}(", ", ", ")")
        }
      case w: Wire => w.sym.toString
    }
    println("Cells:")
    while(rem.nonEmpty) {
      val c = chainStart(rem.head)
      val p = c.principal match {
        case null => ""
        case (w: Wire, _) => s"${w.sym} . "
        case (t, p) => helpers.get((t, p)) match {
          case Some(s) => s"$s . "
          case None =>
            val s = s"$$${nextHelper}"
            nextHelper += 1
            helpers.put(t.getPort(p), s)
            s"$s . "
        }
      }
      println(s"  $p${show(c)}")
    }
  }
}

class Interpreter(globals: Symbols, rules: Iterable[CheckedRule]) extends Scope {

  final class CutKey(val c1: Cell, val c2: Cell) {
    override def hashCode(): Int = c1.hashCode() + c2.hashCode()
    override def equals(obj: Any): Boolean = obj match {
      case o: CutKey => (c1 == o.c1) && (c2 == o.c2) || (c1 == o.c2) && (c2 == o.c1)
      case _ => false
    }
    def ruleKey: RuleKey = new RuleKey(c1.sym, c2.sym)
  }

  final class RuleKey(val s1: Symbol, val s2: Symbol) {
    override def hashCode(): Int = s1.hashCode() + s2.hashCode()
    override def equals(obj: Any): Boolean = obj match {
      case o: RuleKey => (s1 == o.s1) && (s2 == o.s2) || (s1 == o.s2) && (s2 == o.s1)
      case _ => false
    }
    override def toString = s"$s1 . $s2"
  }

  class RuleImpl(val r: AST.Rule, val reduced: Seq[AST.Cut], val args1: Seq[AST.Ident], val args2: Seq[AST.Ident], val key: RuleKey) {
    def args1For(k: RuleKey) = if(k.s1 == key.s1) args1 else args2
    def args2For(k: RuleKey) = if(k.s1 == key.s1) args2 else args1
  }

  def reduce(): Int = {
    val ruleImpls = new mutable.HashMap[RuleKey, RuleImpl]
    rules.foreach { cr =>
      val s1 = globals(cr.name1)
      val s2 = globals(cr.name2)
      val rk = new RuleKey(s1, s2)
      ruleImpls.put(rk, new RuleImpl(cr.r, cr.r.reduced, cr.args1, cr.args2, rk))
    }
    val cuts = mutable.HashSet.empty[CutKey]
    cells.foreach { c =>
      c.principal match {
        case (c2: Cell, 0) =>
          val rk = new RuleKey(c.sym, c2.sym)
          if(ruleImpls.contains(rk))
            cuts.addOne(new CutKey(c, c2))
        case _ =>
      }
    }
    var steps = 0
    while(!cuts.isEmpty) {
      //println(s"Remaining reducible cuts: ${cuts.size}")
      steps += 1
      val c = cuts.head
      cuts.remove(c)
      val r = ruleImpls(c.ruleKey)
      //println(s"Reducing $c with ${r.r.name.s}: ${c.ruleKey}")
      val syms = new Symbols(Some(globals))
      val sc = new Scope
      sc.add(r.reduced, syms)
      //println("***** Reduction:")
      //sc.log()
      val a1 = r.args1For(c.ruleKey).map(syms.getOrAdd)
      val a2 = r.args2For(c.ruleKey).map(syms.getOrAdd)
      val v1 = a1.zipWithIndex.map { case (s, i) => (s, c.c1.getPort(i+1)) }
      val v2 = a2.zipWithIndex.map { case (s, i) => (s, c.c2.getPort(i+1)) }
      val bind = (v1 ++ v2).toMap
      assert(bind.keys.toSet == sc.freeWires.map(_.sym))
      cells.remove(c.c1)
      cells.remove(c.c2)
      cells.addAll(sc.cells)
      sc.freeWires.foreach { w =>
        val (b, bp) = bind(w.sym)
        val (n, np) = w.principal
        b.connect(bp, n, np)
        n.connect(np, b, bp)
        if(bp == 0 && np == 0 && b.isInstanceOf[Cell] && n.isInstanceOf[Cell]) {
          val ck = new CutKey(b.asInstanceOf[Cell], n.asInstanceOf[Cell])
          if(ruleImpls.contains(ck.ruleKey))
            cuts.addOne(ck)
        }
      }
      //println("**** After reduction:")
    }
    steps
  }
}
