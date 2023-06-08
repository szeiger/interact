package de.szeiger.interact

import scala.collection.mutable

sealed trait AnyCheckedRule {
  def show: String
}

class DerivedRule(val deriveName: String, val otherName: String) extends AnyCheckedRule {
  def show = s"$deriveName . $otherName = <derived>"
}

class CheckedMatchRule(creator: => String, val connected: Seq[AST.Expr], val name1: String, val args1: Seq[String], val name2: String, val args2: Seq[String]) extends AnyCheckedRule {
  def show: String = creator
}

class Symbol(val id: String) {
  var refs, arity = 0
  var isCons = false
  var isDef = false
  var returnArity = 1
  def callArity: Int = arity + 1 - returnArity
  var matchContinuationPort: Int = -2
  override def toString: String = id
}

class Symbols(parent: Option[Symbols] = None) {
  private val syms = mutable.HashMap.empty[String, Symbol]
  def newCons(id: String, isDef: Boolean = false, arity: Int = 0, returnArity: Int = 1): Symbol = {
    assert(get(id).isEmpty)
    val sym = new Symbol(id)
    sym.isCons = true
    sym.isDef = isDef
    sym.arity = arity
    sym.returnArity = returnArity
    syms.put(id, sym)
    sym
  }
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

case class ConsAp(target: AST.Ident, tsym: Symbol, args: Seq[AST.Expr]) extends AST.Expr {
  def show = args.map(_.show).mkString(s"<${target.show}>(", ", ", ")")
  def allIdents: Iterator[AST.Ident] = Iterator.single(target) ++ args.iterator.flatMap(_.allIdents)
}

class Model(val statements: Seq[AST.Statement],
  defaultDerive: Seq[String] = Seq("erase", "dup"),
  addEraseDup: Boolean = true) {

  private[this] val ruleCuts = mutable.Map.empty[(String, String), AnyCheckedRule]
  val constrs = mutable.ArrayBuffer.empty[AST.Cons]
  val defs = mutable.ArrayBuffer.empty[AST.Def]
  val data = mutable.ArrayBuffer.empty[AST.Data]
  private[this] val matchRules = mutable.ArrayBuffer.empty[AST.Match]

  def rules: Iterable[AnyCheckedRule] = ruleCuts.values

  private def addDerivedRule(derivedName: String, otherName: String): Unit = {
    val key = if(derivedName <= otherName) (derivedName, otherName) else (otherName, derivedName)
    if(ruleCuts.contains(key)) sys.error(s"Duplicate rule ${derivedName} . ${otherName}")
    ruleCuts.put(key, new DerivedRule(derivedName, otherName))
  }

  private def addDefRules(d: AST.Def): Unit = {
    val dret = AST.Tuple(d.ret.map(AST.Ident))
    val dargst = d.args.tail.map(AST.Ident)
    val di = AST.Ident(d.name)
    d.rules.foreach { r =>
      addMatchRule(AST.Match(AST.Assignment(AST.Ap(di, r.on +: dargst), dret), r.reduced),
        s"${r.on.show} = ${r.reduced.map(_.show).mkString(", ")}")
    }
  }

  private def singleNonIdentIdx(es: Seq[AST.Expr]): Int = {
    val i1 = es.indexWhere(e => !e.isInstanceOf[AST.Ident])
    if(i1 == -1) -1
    else {
      val i2 = es.lastIndexWhere(e => !e.isInstanceOf[AST.Ident])
      if(i2 == i1) i1 else -2
    }
  }

  private def createCurriedDef(ls: Symbol, rs: Symbol, idx: Int, creator: => String): Symbol = {
    val curryId = s"${ls.id}_curry_${rs.id}" //TODO use $ and encode names in bytecode
    globals.get(curryId) match {
      case Some(sym) =>
        assert(sym.isCons)
        if(sym.matchContinuationPort != idx) sys.error("Port mismatch in curried ${ls.id} -> ${rs.id} match in $creator")
        sym
      case None =>
        val largs = (0 until ls.callArity).map(i => s"$$l$i")
        val rargs = (0 until rs.callArity).map(i => s"$$r$i")
        val rcurryArgs = rargs.zipWithIndex.filter(_._2 != idx).map(_._1)
        val sym = globals.newCons(curryId, arity = ls.callArity + rs.callArity - 1, returnArity = ls.returnArity)
        sym.matchContinuationPort = idx
        //println(s"**** left: $ls, $largs")
        //println(s"**** right: $rs, $rargs")
        val curryArgs = largs ++ rcurryArgs
        val curryCons = AST.Cons(curryId, curryArgs, None, None)
        //println(s"**** curryCons: ${curryCons.show}")
        constrs += curryCons
        val fwd = AST.Assignment(AST.Ap(AST.Ident(curryId), curryArgs.map(AST.Ident)), AST.Ident(rargs(idx)))
        //println(curryArgs)
        //println(fwd.show)
        addImpl(new CheckedMatchRule(creator, Seq(fwd), ls.id, largs, rs.id, rargs))
        sym
    }
  }

  private def addImpl(impl: CheckedMatchRule): Unit = {
    val key = if(impl.name1 <= impl.name2) (impl.name1, impl.name2) else (impl.name2, impl.name1)
    if(ruleCuts.contains(key)) sys.error(s"Duplicate rule ${impl.name1} . ${impl.name2}")
    ruleCuts.put(key, impl)
  }

  private def addMatchRule(m: AST.Match, creator: => String): Unit = {
    val on2 = m.on match {
      // complete lhs assignment for raw match rules (already completed for def rules):
      case e: AST.Ap =>
        val s = globals(e.target.s)
        if(s.isDef) {
          assert(e.args.length == s.callArity)
          AST.Assignment(e, AST.Tuple((1 to s.returnArity).map(i => AST.Ident(s"$$ret$i"))))
        } else e
      case e => e
    }
    val unnest = new Normalize(globals)
    val inlined = unnest.toInline(unnest(Seq(on2)).map(unnest.toConsOrder))
    //inlined.foreach(e => println(e.show))
    inlined match {
      case Seq(AST.Assignment(ConsAp(_, ls, largs: Seq[AST.Ident]), ConsAp(_, rs, rargs))) =>
        val compl = if(ls.isDef) largs.takeRight(ls.returnArity) else Nil
        val connected = m.reduced.init :+ connectLastStatement(m.reduced.last, compl)
        addMatchRule(ls, largs, rs, rargs, connected, creator)
      case _ => sys.error(s"Invalid rule: ${m.show}")
    }
  }

  private def addMatchRule(ls: Symbol, largs: Seq[AST.Ident], rs: Symbol, rargs: Seq[AST.Expr], reduced: Seq[AST.Expr], creator: => String): Unit = {
    singleNonIdentIdx(rargs) match {
      case -2 => sys.error(s"Only one nested match allowed in $creator")
      case -1 =>
        addImpl(new CheckedMatchRule(creator, reduced, ls.id, largs.map(_.s), rs.id, rargs.asInstanceOf[Seq[AST.Ident]].map(_.s)))
      case idx =>
        val currySym = createCurriedDef(ls, rs, idx, creator)
        val ConsAp(_, crs, crargs) = rargs(idx)
        val clargs = largs ++ rargs.zipWithIndex.filter(_._2 != idx).map(_._1.asInstanceOf[AST.Ident])
        addMatchRule(currySym, clargs, crs, crargs, reduced, creator)
    }
  }

//  def checkLinearity(cuts: Seq[AST.Cut], free: Set[String], globals: Symbols)(in: => String): Unit = {
//    final class Usages(var count: Int = 0)
//    val usages = mutable.HashMap.from(free.iterator.map(i => (i, new Usages)))
//    val toScan = mutable.Queue.empty[(AST.Cut, AST.Expr)]
//    def scan(c: AST.Cut, e: AST.Expr): Unit = e match {
//      case AST.IdentOrAp(target, args) =>
//        globals.get(target) match {
//          case Some(g) =>
//            if(!g.isCons) sys.error(s"Unexpected global non-constructor symbol $g in $in")
//            if(args.length != g.arity) sys.error(s"Wrong arity ${args.length} != ${g.arity} when using $g in $in")
//          case None =>
//            if(e.isInstanceOf[AST.Ap])
//              sys.error(s"Illegal use of non-constructor symbol $target as constructor in $in")
//            usages.getOrElseUpdate(target, new Usages).count += 1
//        }
//        args.foreach(a => toScan.enqueue((c, a)))
//    }
//    cuts.foreach { c =>
//      scan(c, c.left)
//      scan(c, c.right)
//    }
//    while(!toScan.isEmpty) {
//      val (c, e) = toScan.dequeue()
//      scan(c, e)
//    }
//    val badFree = free.iterator.map(i => (i, usages(i))).filter(_._2.count != 1).toSeq
//    if(badFree.nonEmpty) sys.error(s"Non-linear use of free ${badFree.map(_._1).mkString(", ")} in $in")
//    free.foreach(usages.remove)
//    val badLocal = usages.filter(_._2.count != 2).toSeq
//    if(badLocal.nonEmpty) sys.error(s"Non-linear use of local ${badLocal.map(_._1).mkString(", ")} in $in")
//  }

  // Check Expr and return free identifiers
  private def checkDefs(defs: Seq[AST.Expr])(in: => String): Seq[String] = {
    val locals = new Symbols(None)
    def f(e: AST.Expr): Unit = e match {
      case AST.Assignment(l, r) => f(l); f(r)
      case AST.Tuple(es) => es.foreach(f)
      case AST.Wildcard => ()
      case e @ AST.Ident(s) =>
        val symO = globals.get(s)
        if(symO.exists(_.isCons)) f(AST.Ap(e, Nil))
        else if(symO.isDefined) sys.error(s"Unexpected global non-constructor symbol $s in $in")
        else {
          val sym = locals.getOrAdd(s)
          sym.refs += 1
        }
      case AST.Ap(AST.Ident(s), args) =>
        val symO = globals.get(s)
        if(!symO.exists(_.isCons))
          sys.error(s"Illegal use of non-constructor symbol $s as constructor in $in")
        val a = symO.get.callArity
        if(a != args.length)
          sys.error(s"Wrong number of arguments for $s in $in: got ${args.length}, expected $a")
        args.foreach(f)
    }
    defs.foreach(f)
    val badLocal = locals.symbols.filter(_.refs > 2).toSeq
    if(badLocal.nonEmpty) sys.error(s"Non-linear use of local ${badLocal.map(_.id).mkString(", ")} in $in")
    locals.symbols.filter(_.refs == 1).map(_.id).toSeq
  }

  val globals = new Symbols

  if(addEraseDup) {
    globals.newCons("erase", isDef = true, returnArity = 0)
    globals.newCons("dup", isDef = true, arity = 2, returnArity = 2)
    addDerivedRule("erase", "erase")
    addDerivedRule("erase", "dup")
    addDerivedRule("dup", "dup")
  }

  statements.foreach {
    case c: AST.Cons =>
      if(globals.get(c.name).isDefined) sys.error(s"Duplicate cons/def: ${c.name}")
      c.args.foreach(a => assert(a != null, s"No wildcard parameters allowed in cons: ${c.name}"))
      globals.newCons(c.name, arity = c.args.length)
      constrs += c
    case d: AST.Data => data.addOne(d)
    case d: AST.Def =>
      if(globals.get(d.name).isDefined) sys.error(s"Duplicate cons/def: ${d.name}")
      d.args.tail.foreach(s => assert(s != null, s"In def ${d.name}: Only the principal argument can be a wildcard"))
      globals.newCons(d.name, isDef = true, arity = d.args.length + d.ret.length - 1, returnArity = d.ret.length)
      defs += d
      addDerivedRule("erase", d.name)
      if(d.name != "dup" && d.name != "erase")
        addDerivedRule("dup", d.name)
    case m: AST.Match =>
      matchRules += m
  }

  private def connectLastStatement(e: AST.Expr, extraRhs: Seq[AST.Ident]): AST.Expr = e match {
    case e: AST.Assignment => e
    case e: AST.Tuple =>
      assert(e.exprs.length == extraRhs.length)
      AST.Assignment(AST.Tuple(extraRhs), e)
    case e: AST.Ap =>
      val sym = globals(e.target.s)
      assert(sym.isCons)
      if(sym.returnArity == 0) e
      else {
        assert(sym.returnArity == extraRhs.length)
        AST.Assignment(if(extraRhs.length == 1) extraRhs.head else AST.Tuple(extraRhs), e)
      }
    case e: AST.Ident =>
      assert(extraRhs.length == 1)
      AST.Assignment(extraRhs.head, e)
  }

  defs.foreach(addDefRules)
  constrs.foreach { c =>
    val der = c.der.map(_.constructors).getOrElse(defaultDerive).filter(n => globals.get(n).exists(_.isCons))
    der.foreach { i =>
      if(i == "erase" || i == "dup") addDerivedRule(i, c.name)
      else sys.error(s"Don't know how to derive rule for $i")
    }
  }
  matchRules.foreach(m => addMatchRule(m, s"${m.on.show} = ${m.reduced.map(_.show).mkString(", ")}"))
  data.foreach { d =>
    d.free = checkDefs(d.defs)(d.show)
  }
  rules.foreach {
    case cr: CheckedMatchRule =>
      val free = cr.args1 ++ cr.args2
      val freeSet = free.toSet
      if(freeSet.size != free.size) sys.error(s"Duplicate free symbol in ${cr.show}")
      //checkLinearity(cr.r.reduced, freeSet, globals)(cr.show)
    case _: DerivedRule => ()
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
    data.foreach { d => inter.scope.addExprs(d.defs, new Symbols(Some(globals))) }
  }
}

// Normalize expressions:
// - all compound expressions are unnested (ANF)
// - constructor Idents are converted to Ap
// - only non-constructor Idents can be nested
// - all Ap assignments have the Ap on the RHS
// - all direct assignments are untupled
// - wildcards in assignments are resolved
// - only the last expr can be a non-assignment
class Normalize(globals: Symbols) {
  private var lastTmp = 0
  private def mk(): AST.Ident = { lastTmp += 1; AST.Ident(s"$$u${lastTmp}") }

  def apply(exprs: Seq[AST.Expr]): Seq[AST.Expr] = {
    val assigned = mutable.HashSet.empty[AST.Ident]
    val buf = mutable.ArrayBuffer.empty[AST.Expr]
    def expandWildcards(e: AST.Expr, wild: AST.Ident): AST.Expr = e match {
      case AST.Assignment(ls, rs) =>
        val wild2 = mk()
        val ass2 = AST.Assignment(expandWildcards(ls, wild2), expandWildcards(rs, wild2))
        if(assigned.contains(wild2)) { reorder(unnest(ass2, false)); wild2 }
        else ass2
      case AST.Tuple(es) => AST.Tuple(es.map(expandWildcards(_, wild)))
      case AST.Ap(t, args) => AST.Ap(t, args.map(expandWildcards(_, wild)))
      case AST.Wildcard =>
        if(assigned.contains(wild)) sys.error(s"Duplicate wildcard in assignment")
        assigned += wild
        wild
      case e: AST.Ident => e
    }
    def unnest(e: AST.Expr, nested: Boolean): AST.Expr = e match {
      case AST.Assignment(ls, rs) =>
        if(nested) sys.error("Unexpected nested assignment without wilcard")
        else AST.Assignment(unnest(ls, false), unnest(rs, false))
      case AST.Tuple(es) => AST.Tuple(es.map(unnest(_, true)))
      case AST.IdentOrAp(s, args) =>
        val symO = globals.get(s)
        if(symO.exists(_.isCons) || args.nonEmpty) {
          val ap = AST.Ap(AST.Ident(s), args.map(unnest(_, true)))
          if(nested) {
            val v = mk()
            reorder(AST.Assignment(v, ap))
            v
          } else ap
        } else AST.Ident(s)
    }
    def reorder(e: AST.Expr): Unit = e match {
      case AST.Assignment(ls: AST.Ap, rs: AST.Ap) =>
        val sym1 = globals(ls.target.s)
        val sym2 = globals(rs.target.s)
        if(sym1.returnArity != sym2.returnArity) sys.error(s"Invalid assignments with different arities: $e")
        if(sym1.returnArity == 1) {
          val v = mk()
          buf += AST.Assignment(v, ls)
          buf += AST.Assignment(v, rs)
        } else {
          val vs = (0 until sym1.returnArity).map(_ => mk())
          buf += AST.Assignment(AST.Tuple(vs), ls)
          buf += AST.Assignment(AST.Tuple(vs), rs)
        }
      case AST.Assignment(ls: AST.Ap, rs) => reorder(AST.Assignment(rs, ls))
      case AST.Assignment(AST.Tuple(ls), AST.Tuple(rs)) =>
        ls.zip(rs).foreach { case (l, r) => reorder(AST.Assignment(l, r)) }
      case e => buf += e
    }
    exprs.foreach { e =>
      val wild = mk()
      reorder(unnest(expandWildcards(e, wild), false))
      if(assigned.contains(wild)) sys.error("Unexpected wildcard outside of assignment")
    }
    buf.toSeq
  }

  // reorder assignments as if every def was a cons
  def toConsOrder(e: AST.Expr): AST.Expr = e match {
    case AST.Assignment(id  @ AST.IdentOrTuple(es), AST.Ap(t, args)) =>
      val s = globals(t.s)
      if(!s.isDef) AST.Assignment(id, ConsAp(t, s, args)) else AST.Assignment(args.head, ConsAp(t, s, args.tail ++ es))
    case AST.Ap(t, args) =>
      val s = globals(t.s)
      if(!s.isDef) ConsAp(t, s, args) else AST.Assignment(args.head, ConsAp(t, s, args.tail))
    case e => e
  }

  // convert from cons-order ANF back to inlined expressions
  def toInline(es: Seq[AST.Expr]): Seq[AST.Expr] = {
    if(es.isEmpty) es
    else {
      val vars = mutable.HashMap.from(es.init.map { case AST.Assignment(l, r) => (l, r) })
      def f(e: AST.Expr): AST.Expr = e match {
        case e: AST.Ident => vars.remove(e).map(f).getOrElse(e)
        case e: AST.Tuple => vars.remove(e).map(f).getOrElse(e)
        case ConsAp(target, tsym, args) => ConsAp(target, tsym, args.map(f))
        case AST.Assignment(l, r) => AST.Assignment(f(r), f(l))
      }
      val e2 = f(es.last)
      (vars.iterator.map { case (l, r) => AST.Assignment(l, r) } ++ Iterator.single(e2)).toSeq
    }
  }
}
