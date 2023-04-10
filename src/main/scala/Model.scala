package de.szeiger.interact

import java.io.PrintStream
import scala.collection.mutable

class CheckedRule(val r: AST.Rule, val name1: AST.Ident, val args1: Seq[AST.Ident], val name2: AST.Ident, val args2: Seq[AST.Ident]) {
  def show: String = s"${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}"
}

class RuleKey(_name1: AST.Ident, _name2: AST.Ident) {
  val (name1, name2) =
    if(_name1.s.compareTo(_name2.s) <= 0) (_name1, _name2)
    else (_name2, _name1)
  override def hashCode(): Int = name1.s.hashCode() + name2.s.hashCode()
  override def equals(obj: Any): Boolean = obj match {
    case o: RuleKey => name1.s == o.name1.s && name2.s == o.name2.s
    case _ => false
  }
}

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
  def symbols: Iterator[Symbol] = syms.valuesIterator ++ parent.map(_.symbols).getOrElse(Iterator.empty)
}

trait BaseInterpreter {
  final def log(): Unit = log(System.out)
  def log(out: PrintStream): Unit
  def reduce(): Int
}

class Model(val statements: Seq[AST.Statement]) {
  val constrs = mutable.Map.empty[AST.Ident, AST.Cons]
  val ruleCuts = mutable.Map.empty[RuleKey, CheckedRule]
  val data = mutable.ArrayBuffer.empty[AST.Data]

  def derive(cons: AST.Cons, id: AST.Ident): AST.Rule = {
    var nextId = 0
    def genId() = {
      val s = AST.Ident(s"$$s${nextId}")
      nextId += 1
      s
    }
    val (cut, reduced) = id.s match {
      case "Erase" =>
        val Erase = AST.Ident("Erase")
        val ids = (0 until cons.arity).map(_ => genId()).toArray
        val cut = AST.Cut(Erase, AST.Ap(cons.name, ids))
        val reduced = ids.map(i => AST.Cut(Erase, i))
        (cut, reduced.toSeq)
      case "Dup" =>
        val Dup = AST.Ident("Dup")
        val ids, aIds, bIds = (0 until cons.arity).map(_ => genId()).toArray
        val a, b = genId()
        val cut = AST.Cut(AST.Ap(Dup, Seq(a, b)), AST.Ap(cons.name, ids))
        val dupPorts = ids.zip(aIds).zip(bIds).map { case ((id, aId), bId) =>
          AST.Cut(AST.Ap(Dup, Seq(aId, bId)), id)
        }
        val recombA = AST.Cut(a, AST.Ap(cons.name, aIds))
        val recombB = AST.Cut(b, AST.Ap(cons.name, bIds))
        (cut, recombA :: recombB :: dupPorts.toList)
      case s => sys.error(s"Don't know how to derive ${cons.name.s} . ${id.s}")
    }
    AST.Rule(cut, reduced)
  }

  def addRule(r: AST.Rule): Unit = {
    def checkCutCell(e: AST.Expr): (AST.Ident, Seq[AST.Ident]) = e match {
      case a: AST.Ap =>
        val args = a.args.map {
          case i: AST.Ident => i
          case _ => sys.error(s"No nested patterns allowed in rule ${r.cut.show}")
        }
        (a.target, args)
      case a: AST.Ident =>
        (a, Nil)
    }
    val (n1, a1) = checkCutCell(r.cut.left)
    val (n2, a2) = checkCutCell(r.cut.right)
    val impl = new CheckedRule(r, n1, a1, n2, a2)
    val key = new RuleKey(impl.name1, impl.name2)
    if(ruleCuts.contains(key)) sys.error(s"Rule ${r.cut.show} duplicates ${impl.name1.s} . ${impl.name2.s}")
    ruleCuts.put(key, impl)
  }

  def checkLinearity(cuts: Seq[AST.Cut], free: Set[AST.Ident], globals: Symbols)(in: => String): Unit = {
    final class Usages(var count: Int = 0)
    val usages = mutable.HashMap.from(free.iterator.map(i => (i, new Usages)))
    val toScan = mutable.Queue.empty[(AST.Cut, AST.Expr)]
    def scan(c: AST.Cut, e: AST.Expr): Unit = {
      globals.get(e.target) match {
        case Some(g) =>
          if(!g.isCons) sys.error(s"Unexpected global non-constructor symbol $g in $in")
          if(e.args.length != g.cons.arity) sys.error(s"Wrong arity ${e.args.length} != ${g.cons.arity} when using $g in $in")
        case None =>
          if(e.isInstanceOf[AST.Ap])
            sys.error(s"Illegal use of non-constructor symbol ${e.target.show} as constructor in $in")
          usages.getOrElseUpdate(e.target, new Usages).count += 1
      }
      e.args.foreach(a => toScan.enqueue((c, a)))
    }
    cuts.foreach { c =>
      scan(c, c.left)
      scan(c, c.right)
    }
    while(!toScan.isEmpty) {
      val (c, e) = toScan.dequeue()
      scan(c, e)
    }
    val badFree = free.iterator.map(i => (i, usages(i))).filter(_._2.count != 1).toSeq
    if(badFree.nonEmpty) sys.error(s"Non-linear use of free ${badFree.map(_._1.show).mkString(", ")} in $in")
    free.foreach(usages.remove)
    val badLocal = usages.filter(_._2.count != 2).toSeq
    if(badLocal.nonEmpty) sys.error(s"Non-linear use of local ${badLocal.map(_._1.show).mkString(", ")} in $in")
  }

  statements.foreach {
    case c: AST.Cons =>
      if(constrs.contains(c.name)) sys.error(s"Duplicate cons: ${c.name.s}")
      constrs.put(c.name, c)
      c.der.foreach { der =>
        der.constructors.foreach(i => addRule(derive(c, i)))
      }
      c.rules.foreach { m =>
        addRule(AST.Rule(AST.Cut(AST.Ap(c.name, c.args), m.rhs), m.reduced))
      }
    case r: AST.Rule => addRule(r)
    case d: AST.Data => data.addOne(d)
  }

  val globals = new Symbols
  constrs.values.foreach { c =>
    globals.getOrAdd(c.name).cons = c
  }

  data.foreach { d =>
    val freeSet = d.free.toSet
    if(freeSet.size != d.free.size) sys.error(s"Duplicate free symbol in ${d.show}")
    checkLinearity(d.cuts, freeSet, globals)(d.show)
  }
  ruleCuts.foreach { case (rk, cr) =>
    val free = cr.args1 ++ cr.args2
    val freeSet = free.toSet
    if(freeSet.size != free.size) sys.error(s"Duplicate free symbol in ${cr.show}")
    checkLinearity(cr.r.reduced, freeSet, globals)(cr.show)
  }

  def createSTInterpreter: BaseInterpreter = {
    val i = new st.Interpreter(globals, ruleCuts.values)
    data.foreach(d => i.add(d.cuts, new Symbols(Some(globals))))
    i
  }

  def createMTInterpreter: mt.Interpreter = {
    val i = new mt.Interpreter(globals, ruleCuts.values)
    data.foreach(d => i.add(d.cuts, new Symbols(Some(globals))))
    i
  }
}
