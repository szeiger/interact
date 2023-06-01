package de.szeiger.interact

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class CheckedRule(val r: AST.Rule, val name1: String, val args1: Seq[String], val name2: String, val args2: Seq[String]) {
  def show: String = s"${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}"
}

class Symbol(val id: String) {
  var refs, arity = 0
  var isCons = false
  var isDef = false
  var returnArity = 1
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
  val constrs = mutable.ArrayBuffer.empty[AST.Cons]
  val defs = mutable.ArrayBuffer.empty[AST.Def]
  val data = mutable.ArrayBuffer.empty[AST.Data]

  def rules: Iterable[CheckedRule] = ruleCuts.values

  def derive(consName: String, arity: Int, id: String): AST.Rule = {
    var nextId = 0
    def genId() = {
      val s = AST.Ident(s"$$s${nextId}")
      nextId += 1
      s
    }
    val (cut, reduced) = id match {
      case "Erase" =>
        val Erase = AST.Ident("Erase")
        val ids = (0 until arity).map(_ => genId()).toArray
        val cut = AST.Cut(Erase, AST.Ap(AST.Ident(consName), ids))
        val reduced = ids.map(i => AST.Cut(Erase, i))
        (cut, reduced.toSeq)
      case "Dup" =>
        val Dup = AST.Ident("Dup")
        val ids, aIds, bIds = (0 until arity).map(_ => genId()).toArray
        val a, b = genId()
        val cut = AST.Cut(AST.Ap(Dup, Seq(a, b)), AST.Ap(AST.Ident(consName), ids))
        val dupPorts = ids.zip(aIds).zip(bIds).map { case ((id, aId), bId) =>
          AST.Cut(AST.Ap(Dup, Seq(aId, bId)), id)
        }
        val recombA = AST.Cut(a, AST.Ap(AST.Ident(consName), aIds))
        val recombB = AST.Cut(b, AST.Ap(AST.Ident(consName), bIds))
        (cut, recombA :: recombB :: dupPorts.toList)
      case s => sys.error(s"Don't know how to derive ${consName} . $id")
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
    def scan(c: AST.Cut, e: AST.Expr): Unit = e match {
      case AST.IdentOrAp(target, args) =>
        globals.get(target) match {
          case Some(g) =>
            if(!g.isCons) sys.error(s"Unexpected global non-constructor symbol $g in $in")
            if(args.length != g.arity) sys.error(s"Wrong arity ${args.length} != ${g.arity} when using $g in $in")
          case None =>
            if(e.isInstanceOf[AST.Ap])
              sys.error(s"Illegal use of non-constructor symbol $target as constructor in $in")
            usages.getOrElseUpdate(target, new Usages).count += 1
        }
        args.foreach(a => toScan.enqueue((c, a)))
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

  val globals = new Symbols

  statements.foreach {
    case c: AST.Cons =>
      if(globals.get(c.name).isDefined) sys.error(s"Duplicate cons/def: ${c.name}")
      c.args.foreach(a => assert(a != null, s"No wildcard parameters allowed in cons: ${c.name}"))
      val s = globals.getOrAdd(c.name)
      s.arity = c.args.length
      s.isCons = true
      constrs += c
      c.der.foreach { der =>
        der.constructors.foreach(i => addRule(derive(c.name, c.args.length, i)))
      }
      c.rules.foreach { r =>
        addRule(AST.Rule(AST.Cut(AST.Ap(AST.Ident(c.name), c.args.map(AST.Ident)), r.rhs), r.reduced, false))
      }
    case r: AST.Rule => addRule(r)
    case d: AST.Data => data.addOne(d)
    case d: AST.Def =>
      if(globals.get(d.name).isDefined) sys.error(s"Duplicate cons/def: ${d.name}")
      d.args.tail.foreach(s => assert(s != null, s"In def ${d.name}: Only the principal argument can be a wildcard"))
      val s = globals.getOrAdd(d.name)
      s.arity = d.args.length + d.ret.length - 1
      s.isCons = true
      s.isDef = true
      s.returnArity = d.ret.length
      defs += d
      addRule(derive(d.name, s.arity, "Erase"))
      if(d.name != "Dup" && d.name != "Erase")
        addRule(derive(d.name, s.arity, "Dup"))
  }

  private def cutArgs[T](sym: Symbol, args: Seq[T], ret: Seq[T]): Seq[T] =
    if(sym.isDef) args.tail ++ ret else args

  private def simpleArgs(es: Seq[AST.Expr]): Seq[String] = es.map {
    case AST.Ident(s) => s
    case AST.Wildcard => null
  }

  private def defArgs(e: AST.DefExpr): (Symbol, Seq[String], Seq[String]) = e match {
    case AST.Assignment(lhs, rhs) =>
      val AST.ExprSpec(lname, largs) = lhs
      val AST.ExprSpec(rname, rargs) = rhs
      assert((lname == null) != (rname == null))
      val (n, as, rs) = if(lname == null) (rname, rargs, largs) else (lname, largs, rargs)
      val sym = globals(n)
      assert(sym.isCons)
      (sym, simpleArgs(as), simpleArgs(rs))
    case AST.ExprSpec(name, args) =>
      assert(name != null)
      val sym = globals(name)
      assert(sym.isCons)
      (sym, simpleArgs(args), null)
  }

  private def defExprToCut(e: AST.DefExpr): AST.Cut = {
    def create(t: AST.Ident, args: Seq[AST.Expr]): AST.Cut =
      AST.Cut(args.head, AST.Ap(t, args.tail))
    def toCutOrder(s: Symbol, args: Seq[AST.Expr]): Seq[AST.Expr] = {
      assert(s.isCons)
      if(s.isDef) {
        val (a1, a2) = args.splitAt(s.returnArity)
        a2 ++ a1
      } else args
    }
    e match {
      case AST.Assignment(l, AST.Ap(t, args)) =>
        val ret = l match {
          case AST.Tuple(ret) => ret
          case ret: AST.Ident => Seq(ret)
        }
        create(t, toCutOrder(globals(t.s), ret ++ args))
      case AST.Assignment(l: AST.Ident, r: AST.Ident) => AST.Cut(l, r)
      case AST.Ap(t, args) =>
        val s = globals(t.s)
        assert(s.isDef)
        assert(s.returnArity == 0)
        create(t, args)
    }
  }

  private def connectLastStatement(e: AST.DefExpr, extraRhs: Seq[AST.Ident]): AST.Assignment = e match {
    case e: AST.Assignment => e
    case e: AST.Tuple =>
      assert(e.exprs.length == extraRhs.length)
      AST.Assignment(AST.Tuple(extraRhs), e)
    case e: AST.Ap =>
      val sym = globals(e.target.s)
      assert(sym.isCons)
      assert(sym.returnArity == extraRhs.length)
      AST.Assignment(if(extraRhs.length == 1) extraRhs.head else AST.Tuple(extraRhs), e)
    case e: AST.Ident =>
      assert(extraRhs.length == 1)
      AST.Assignment(extraRhs.head, e)
  }

  defs.foreach { d =>
    val dsym = globals(d.name)
    val danames = cutArgs(dsym, d.args, d.ret)
    val dret = d.ret.map(AST.Ident)
    //println(s"***** def ${d.show}")
    d.rules.foreach { r =>
      val unnest = new Unnest(globals)
      val (osym, oas, ors) = defArgs(r.on)
      val oanames = cutArgs(osym, oas, ors)
      //println(s"  $osym, $oas, $ors")
      val cutLhs = AST.Ap(AST.Ident(d.name), danames.map(AST.Ident))
      val cutRhs = AST.Ap(AST.Ident(osym.id), oanames.map(AST.Ident))
      //println(s"  ${AST.Cut(cutLhs, cutRhs).show}")
      //println(s"    original:")
      //r.reduced.foreach(e => println(s"    - ${e.show}"))
      val connected = r.reduced.init :+ connectLastStatement(r.reduced.last, dret)
      //println(s"    connected:")
      //connected.foreach(e => println(s"    - ${e.show}"))
      val unnested = unnest(connected)
      //println(s"    unnested:")
      //unnested.foreach(e => println(s"    - ${e.show}"))
      val cuts = unnested.map(defExprToCut)
      //println(s"    cuts:")
      //cuts.foreach(e => println(s"    - ${e.show}"))
      addRule(AST.Rule(AST.Cut(cutLhs, cutRhs), cuts, false))
    }
  }

  data.foreach { d =>
    val freeSet = d.free.toSet
    if(freeSet.size != d.free.size) sys.error(s"Duplicate free symbol in ${d.show}")
    checkLinearity(d.cuts, freeSet, globals)(d.show)
  }
  rules.foreach { cr =>
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

// Convert expressions to ANF
// - all compound expressions are unnested
// - only nullary non-constructor Idents can be nested
// - nullary constructor Idents are converted to Ap
// - all Ap assignments have the Ap on the RHS
// - all direct assignments are untupled
class Unnest(globals: Symbols) {
  private var lastTmp = 0
  private def mk(): AST.Ident = { lastTmp += 1; AST.Ident(s"$$u${lastTmp}") }

  def apply(es: Seq[AST.DefExpr]): Seq[AST.DefExpr] = es.flatMap(apply)

  def apply(e: AST.DefExpr): Seq[AST.DefExpr] = e match {
    case AST.Assignment(l, r) =>
      val (l1, ls) = applyExpr(l)
      val (r1, rs) = applyExpr(r)
      (l1, r1) match {
        case (AST.Tuple(ls2), AST.Tuple(rs2)) if(ls2.nonEmpty) =>
          assert(ls2.length == rs2.length)
          val as = ls2.zip(rs2).map { case (l, r) => AST.Assignment(l, r) }
          ls ++ rs ++ as
        case (e1, e2: AST.Tuple) if !e1.isInstanceOf[AST.Tuple] =>
          ls ++ rs :+ AST.Assignment(e2, e1)
        case _ => ls ++ rs :+ AST.Assignment(l1, r1)
      }
    case (e: AST.Expr) =>
      val (e2, ass) = applyExpr(e)
      ass :+ e2
  }

  def applyExpr(e: AST.Expr): (AST.Expr, Seq[AST.Assignment]) = {
    val buf = ArrayBuffer.empty[AST.Assignment]
    def assign(e: AST.Ap): AST.Expr = {
      val ts = globals(e.target.s)
      val v: AST.Expr = if(ts.returnArity == 1) mk() else AST.Tuple((1 to ts.returnArity).map(_ => mk()))
      buf += AST.Assignment(v, f(AST.Ap(e.target, e.args)))
      v
    }
    def f(e: AST.Expr): AST.Expr = e match {
      case AST.Tuple(Seq(e)) => f(e)
      case AST.Tuple(es) => AST.Tuple(es.map(f))
      case AST.Ap(t, args) =>
        AST.Ap(t, args.map {
          case e: AST.Ident =>
            val s = globals.get(e.s)
            if(s.exists(_.isCons)) assign(AST.Ap(e, Nil)) else e
          case e: AST.Ap => assign(e)
        })
      case e: AST.Ident =>
        val s = globals.get(e.s)
        if(s.exists(_.isCons)) AST.Ap(e, Nil) else e
    }
    (f(e), buf.toSeq)
  }
}
