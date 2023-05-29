package de.szeiger.interact

import scala.collection.mutable

class CheckedRule(val r: AST.Rule, val name1: String, val args1: Seq[String], val name2: String, val args2: Seq[String]) {
  def show: String = s"${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}"
}

class Symbol(val id: String) {
  var refs = 0
  var cons: AST.Cons = null
  def isCons = cons != null
  def arity = if(cons != null) cons.arity else 0
  override def toString = id
}

class Symbols(parent: Option[Symbols] = None) {
  private val syms = mutable.HashMap.empty[String, Symbol]
  def getOrAdd(id: String): Symbol = {
    val so = parent match {
      case Some(p) => p.syms.get(id)
      case None => None
    }
    so.getOrElse(syms.getOrElseUpdate(id, new Symbol(id)))
  }
  def get(id: String): Option[Symbol] = {
    val so = parent match {
      case Some(p) => p.syms.get(id)
      case None => None
    }
    so.orElse(syms.get(id))
  }
  def apply(id: String): Symbol =
    get(id).getOrElse(sys.error(s"No symbol found for $id"))
  def symbols: Iterator[Symbol] = syms.valuesIterator ++ parent.map(_.symbols).getOrElse(Iterator.empty)
}

trait BaseInterpreter {
  def scope: Analyzer[_]
  def reduce(): Int
}

class Model(val statements: Seq[AST.Statement]) {
  private[this] val ruleCuts = mutable.Map.empty[(String, String), CheckedRule]
  val constrs = mutable.Map.empty[String, AST.Cons]
  val data = mutable.ArrayBuffer.empty[AST.Data]

  def rules: Iterable[CheckedRule] = ruleCuts.values

  def derive(cons: AST.Cons, id: String): AST.Rule = {
    var nextId = 0
    def genId() = {
      val s = AST.Ident(s"$$s${nextId}")
      nextId += 1
      s
    }
    val (cut, reduced) = id match {
      case "Erase" =>
        val Erase = AST.Ident("Erase")
        val ids = (0 until cons.arity).map(_ => genId()).toArray
        val cut = AST.Cut(Erase, AST.Ap(AST.Ident(cons.name), ids))
        val reduced = ids.map(i => AST.Cut(Erase, i))
        (cut, reduced.toSeq)
      case "Dup" =>
        val Dup = AST.Ident("Dup")
        val ids, aIds, bIds = (0 until cons.arity).map(_ => genId()).toArray
        val a, b = genId()
        val cut = AST.Cut(AST.Ap(Dup, Seq(a, b)), AST.Ap(AST.Ident(cons.name), ids))
        val dupPorts = ids.zip(aIds).zip(bIds).map { case ((id, aId), bId) =>
          AST.Cut(AST.Ap(Dup, Seq(aId, bId)), id)
        }
        val recombA = AST.Cut(a, AST.Ap(AST.Ident(cons.name), aIds))
        val recombB = AST.Cut(b, AST.Ap(AST.Ident(cons.name), bIds))
        (cut, recombA :: recombB :: dupPorts.toList)
      case s => sys.error(s"Don't know how to derive ${cons.name} . $id")
    }
    AST.Rule(cut, reduced, true)
  }

  def addRule(r: AST.Rule): Unit = {
    def checkCutCell(e: AST.Expr): (String, Seq[String]) = e match {
      case a: AST.Ap =>
        val args = a.args.map {
          case i: AST.Ident => i.s
          case _ => sys.error(s"No nested patterns allowed in rule ${r.cut.show}")
        }
        (a.target.s, args)
      case a: AST.Ident =>
        (a.s, Nil)
    }
    val (n1, a1) = checkCutCell(r.cut.left)
    val (n2, a2) = checkCutCell(r.cut.right)
    val impl = new CheckedRule(r, n1, a1, n2, a2)
    val key = if(impl.name1 <= impl.name2) (impl.name1, impl.name2) else (impl.name2, impl.name1)
    if(ruleCuts.contains(key)) sys.error(s"Rule ${r.cut.show} duplicates ${impl.name1} . ${impl.name2}")
    ruleCuts.put(key, impl)
  }

  def checkLinearity(cuts: Seq[AST.Cut], free: Set[String], globals: Symbols)(in: => String): Unit = {
    final class Usages(var count: Int = 0)
    val usages = mutable.HashMap.from(free.iterator.map(i => (i, new Usages)))
    val toScan = mutable.Queue.empty[(AST.Cut, AST.Expr)]
    def scan(c: AST.Cut, e: AST.Expr): Unit = {
      globals.get(e.target.s) match {
        case Some(g) =>
          if(!g.isCons) sys.error(s"Unexpected global non-constructor symbol $g in $in")
          if(e.args.length != g.cons.arity) sys.error(s"Wrong arity ${e.args.length} != ${g.cons.arity} when using $g in $in")
        case None =>
          if(e.isInstanceOf[AST.Ap])
            sys.error(s"Illegal use of non-constructor symbol ${e.target.show} as constructor in $in")
          usages.getOrElseUpdate(e.target.s, new Usages).count += 1
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
    if(badFree.nonEmpty) sys.error(s"Non-linear use of free ${badFree.map(_._1).mkString(", ")} in $in")
    free.foreach(usages.remove)
    val badLocal = usages.filter(_._2.count != 2).toSeq
    if(badLocal.nonEmpty) sys.error(s"Non-linear use of local ${badLocal.map(_._1).mkString(", ")} in $in")
  }

  statements.foreach {
    case c: AST.Cons =>
      if(constrs.contains(c.name)) sys.error(s"Duplicate cons: ${c.name}")
      constrs.put(c.name, c)
      c.der.foreach { der =>
        der.constructors.foreach(i => addRule(derive(c, i)))
      }
      c.rules.foreach { m =>
        addRule(AST.Rule(AST.Cut(AST.Ap(AST.Ident(c.name), c.args.map(AST.Ident)), m.rhs), m.reduced, false))
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

  def createMTInterpreter(numThreads: Int, compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : mt.Interpreter =
    new mt.Interpreter(globals, rules, numThreads, compile, debugLog, debugBytecode, collectStats)

  def createST2Interpreter(compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : st2.Interpreter =
    new st2.Interpreter(globals, rules, compile, debugLog, debugBytecode, collectStats)

  def createST3Interpreter(compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : st3.Interpreter =
    new st3.Interpreter(globals, rules, compile, debugLog, debugBytecode, collectStats)

  def createInterpreter(spec: String, debugLog: Boolean = false,
      debugBytecode: Boolean = false, collectStats: Boolean = false): BaseInterpreter = {
    spec match {
      case s"st2.i" => createST2Interpreter(compile = false, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"st2.c" => createST2Interpreter(compile = true, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"st3.i" => createST3Interpreter(compile = false, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"st3.c" => createST3Interpreter(compile = true, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"mt${mode}.i" => createMTInterpreter(mode.toInt, compile = false, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"mt${mode}.c" => createMTInterpreter(mode.toInt, compile = true, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
    }
  }

  def setData(inter: BaseInterpreter): Unit = {
    inter.scope.clear()
    data.foreach(d => inter.scope.add(d.cuts, new Symbols(Some(globals))))
  }
}
