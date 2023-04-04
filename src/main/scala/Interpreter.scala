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
  def principal: (Target, Int)
  def connect(slot: Int, t: Target, tslot: Int): Unit
  def getPort(slot: Int): (Target, Int)
  def allPorts: Iterator[(Target, Int)]
}

final class Wire(val sym: Symbol) extends Target {
  private[this] var ptarget: Target = _
  private[this] var pport: Int = _
  def principal: (Target, Int) = (ptarget, pport)
  def connect(slot: Int, t: Target, tslot: Int): Unit = {
    ptarget = t
    pport = tslot
  }
  def getPort(slot: Int): (Target, Int) = principal
  def allPorts: Iterator[(Target, Int)] = Iterator.single(principal)
}

final class Cell(val sym: Symbol, val arity: Int) extends Target {
  private[this] val targets = new Array[Target](arity+1)
  private[this] val ports = new Array[Int](arity+1)
  override def connect(slot: Int, t: Target, tslot: Int) = {
    targets(slot) = t
    ports(slot) = tslot
  }
  override def getPort(slot: Int): (Target, Int) =
    (targets(slot), ports(slot))
  def principal: (Target, Int) = (targets(0), ports(0))
  def allAux: Iterator[(Target, Int)] = allPorts.drop(1)
  def allPorts: Iterator[(Target, Int)] = targets.iterator.zip(ports.iterator)
  override def toString = s"Cell($sym, $arity, ${allPorts.map { case (t, p) => s"(${if(t == null) "null" else "_"},$p)" }.mkString(", ") })"
}

class Scope {
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

  def reachableCells: Iterator[Cell] = {
    val s = mutable.HashSet.empty[Cell]
    def cellTargets(t: Target) = t.allPorts.map(_._1).collect { case c: Cell => c }
    val q = mutable.Queue.from(freeWires.flatMap(cellTargets))
    while(!q.isEmpty) {
      val w = q.dequeue()
      if(s.add(w)) q.enqueueAll(cellTargets(w))
    }
    s.iterator
  }

  def log(): Unit = {
    println(s"Free wires: ${freeWires.map(_.sym).mkString(", ")}")
    val rem = mutable.HashSet.from(reachableCells)
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
          if(c.sym.id.s == "Cons" && c.arity == 2 && c.getPort(1)._2 == 0 && c.getPort(2)._2 == 0) {
            val lhs = targetOrReplacement(c.getPort(1)._1, c.getPort(1)._2)
            val rhs = targetOrReplacement(c.getPort(2)._1, c.getPort(2)._2)
            s"$lhs :: $rhs"
          } else if(c.arity == 0) c.sym.toString
          else c.allAux.map { case (t, p) => targetOrReplacement(t, p) }.mkString(s"${c.sym}(", ", ", ")")
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
    override def toString = s"CutKey($c1, $c2)"
  }

  final class RuleKey(val s1: Symbol, val s2: Symbol) {
    override def hashCode(): Int = s1.hashCode() + s2.hashCode()
    override def equals(obj: Any): Boolean = obj match {
      case o: RuleKey => (s1 == o.s1) && (s2 == o.s2) || (s1 == o.s2) && (s2 == o.s1)
      case _ => false
    }
    override def toString = s"$s1 . $s2"
  }

  final case class ProtoCell(sym: Symbol, arity: Int, wires: Array[Int], ports: Array[Int]) {
    override def toString = s"ProtoCell($sym, $arity, ${wires.mkString("[",",","]")}, ${ports.mkString("[",",","]")})"
  }

  final class RuleImpl(val r: AST.Rule, val reduced: Seq[AST.Cut], val args1: Seq[AST.Ident], val args2: Seq[AST.Ident], val key: RuleKey) {
    def args1For(k: RuleKey) = if(k.s1 == key.s1) args1 else args2
    def args2For(k: RuleKey) = if(k.s1 == key.s1) args2 else args1

    var protoCells: Array[ProtoCell] = _
    var freeWires: Array[Int] = _
    var freePorts: Array[Int] = _

    def prepare(globals: Symbols): Unit = {
      //println(s"***** Preparing ${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}")
      val syms = new Symbols(Some(globals))
      val sc = new Scope
      sc.add(r.reduced, syms)
      //sc.log()
      val cells = sc.reachableCells.toArray
      val freeLookup = sc.freeWires.iterator.map { w => (w.sym, w) }.toMap
      val wires = (args1 ++ args2).map { i => freeLookup(syms(i)) }.toArray
      val lookup = (cells.iterator.zipWithIndex ++ wires.iterator.zipWithIndex.map { case (w, p) => (w, -p-1) }).toMap
      protoCells = cells.map { c =>
        new ProtoCell(c.sym, c.arity, c.allPorts.map(_._1).map(lookup).toArray, c.allPorts.map(_._2).toArray)
      }
      freeWires = wires.map(w => lookup(w.principal._1))
      freePorts = wires.map(_.principal._2)
      //protoCells.foreach(println)
      //wires.map(_.sym).zip(freeWires).zip(freePorts).map { case ((s, t), p) => s"$s: ($t, $p)" }.foreach(println)
    }

    def reduce(cut1: Cell, cut2: Cell): Iterable[CutKey] = {
      val cells = protoCells.map { pc => new Cell(pc.sym, pc.arity) }
      var i = 0
      while(i < cells.length) {
        var j = 0
        val pc = protoCells(i)
        while(j < pc.arity+1) {
          val w = pc.wires(j)
          if(w >= 0) cells(i).connect(j, cells(w), pc.ports(j))
          j += 1
        }
        i += 1
      }
      i = 0
      def cutTarget(i: Int) = if(i < cut1.arity) cut1.getPort(i+1) else cut2.getPort(i+1-cut1.arity)
      val ret = new mutable.HashSet[CutKey]
      while(i < freeWires.length) {
        val (t, p) = cutTarget(i)
        val fw = freeWires(i)
        //println(s"Connecting freeWire($i): $t, $p, $fw")
        val (wt, wp) =
          if(fw >= 0) (cells(fw), freePorts(i))
          else cutTarget(-1-fw)
        t.connect(p, wt, wp)
        wt.connect(wp, t, p)
        if(p == 0 && wp == 0 && t.isInstanceOf[Cell] && wt.isInstanceOf[Cell])
          ret.addOne(new CutKey(t.asInstanceOf[Cell], wt.asInstanceOf[Cell]))
        i += 1
      }
      //cells.foreach { c => println(s"created $c") }
      ret
    }
  }

  def reduce(): Int = {
    val ruleImpls = new mutable.HashMap[RuleKey, RuleImpl]
    rules.foreach { cr =>
      val s1 = globals(cr.name1)
      val s2 = globals(cr.name2)
      val rk = new RuleKey(s1, s2)
      val ri = new RuleImpl(cr.r, cr.r.reduced, cr.args1, cr.args2, rk)
      ri.prepare(globals)
      ruleImpls.put(rk, ri)
    }
    val cutsMap = mutable.HashMap.empty[CutKey, RuleImpl]
    reachableCells.foreach { c =>
      c.principal match {
        case (c2: Cell, 0) =>
          val rk = new RuleKey(c.sym, c2.sym)
          val ri = ruleImpls.getOrElse(rk, null)
          if(ri != null)
            cutsMap.addOne((new CutKey(c, c2), ri))
        case _ =>
      }
    }
    val cuts = mutable.ArrayBuffer.from(cutsMap)
    var steps = 0
    while(!cuts.isEmpty) {
      var cutRule = cuts.last
      cuts.dropRightInPlace(1)
      while(cutRule != null) {
        //println(s"Remaining reducible cuts: ${cuts.size+1}")
        steps += 1
        val cut = cutRule._1
        val r = cutRule._2
        //println(s"Reducing $cut with ${r.r.cut.show}: ${cut.ruleKey}")
        cutRule = null
        val (c1, c2) = if(cut.ruleKey.s1 == r.key.s1) (cut.c1, cut.c2) else (cut.c2, cut.c1)
        r.reduce(c1, c2).foreach { ck =>
          val ri = ruleImpls.getOrElse(ck.ruleKey, null)
          if(ri != null) {
            if(cutRule == null) cutRule = (ck, ri)
            else cuts.addOne((ck, ri))
          }
        }
        //println("**** After reduction:")
        //log()
      }
    }
    steps
  }
}
