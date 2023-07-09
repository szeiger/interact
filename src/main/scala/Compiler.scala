package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable

sealed trait CheckedRule {
  def show: String
  def name1: String
  def name2: String
}

class DerivedRule(val name1: String, val name2: String) extends CheckedRule {
  def show = s"$name1 . $name2 = <derived>"
}

class CheckedMatchRule(val reduction: Seq[Branch], val name1: String, val args1: Seq[Ident], val name2: String, val args2: Seq[Ident],
    val emb1: Option[Ident], val emb2: Option[Ident]) extends CheckedRule {
  def show: String = {
    def on(n: String, e: Option[Ident], as: Seq[Ident]): String =
      s"$n${e.map(s => s"[${s.show}]").getOrElse("")}(${as.map(_.s).mkString(", ")})"
    s"match ${on(name1, emb1, args1)} = ${on(name2, emb2, args2)} ${Branch.show(reduction)}"
  }
}

trait BaseInterpreter {
  def scope: Analyzer[_]
  def reduce(): Int
}

class Compiler(val unit: CompilationUnit,
  defaultDerive: Seq[String] = Seq("erase", "dup"),
  addEraseDup: Boolean = true) {

  val global = new Global
  import global._

  private[this] val prepare = new Prepare(global)
  private[this] val checkedRules = mutable.Map.empty[(String, String), CheckedRule]

  if(addEraseDup) {
    globalSymbols.define("erase", isCons = true, isDef = true, returnArity = 0)
    globalSymbols.define("dup", isCons = true, isDef = true, arity = 2, returnArity = 2)
    addChecked(new DerivedRule("erase", "erase"))
    addChecked(new DerivedRule("erase", "dup"))
    addChecked(new DerivedRule("dup", "dup"))
  }
  prepare.apply(unit)

  private[this] val data = mutable.ArrayBuffer.empty[Let]
  unit.statements.foreach {
    case c: Cons =>
      addDerivedRules(c.der.getOrElse(defaultDerive.map(Ident(_))).filter(n => globalSymbols.get(n.s).exists(_.isCons)), c.name)
    case d: Def =>
      addDefRules(d)
      addChecked(new DerivedRule("erase", d.name.s))
      if(d.name.s != "dup" && d.name.s != "erase")
        addChecked(new DerivedRule("dup", d.name.s))
    case l: Let => data += l
    case m: Match =>
      addMatchRule(m)
  }

  checkedRules.values.foreach {
    case cr: CheckedMatchRule =>
      val free = cr.args1 ++ cr.args2
      val freeSet = free.toSet
      if(freeSet.size != free.size) sys.error(s"Duplicate free symbol in ${cr.show}")
    case _: DerivedRule => ()
  }

  checkThrow()

  private def addDerivedRules(names1: Seq[Ident], name2: Ident): Unit = {
    names1.foreach { i =>
      if(i.s == "erase" || i.s == "dup") addChecked(new DerivedRule(i.s, name2.s))
      else error(s"Don't know how to derive '${i.s}'", i)
    }
  }

  private def addDefRules(d: Def): Unit = {
    d.rules.foreach { r =>
      val dret = Tuple(d.ret).setPos(d.pos)
      addMatchRule(Match(Assignment(Apply(d.name, d.embeddedId, r.on ++ d.args.drop(r.on.length)).setPos(d.pos), dret).setPos(r.pos), r.reduced).setPos(r.pos))
    }
  }

  private def connectLastStatement(e: Expr, extraRhs: Seq[Ident]): Expr = e match {
    case e: Assignment => e
    case e: Tuple =>
      assert(e.exprs.length == extraRhs.length)
      Assignment(Tuple(extraRhs).setPos(extraRhs.head.pos), e).setPos(extraRhs.head.pos)
    case e: Apply =>
      val sym = globalSymbols(e.target.s)
      assert(sym.isCons)
      if(sym.returnArity == 0) e
      else {
        assert(sym.returnArity == extraRhs.length)
        Assignment(if(extraRhs.length == 1) extraRhs.head else Tuple(extraRhs).setPos(extraRhs.head.pos), e).setPos(extraRhs.head.pos)
      }
    case e: Ident =>
      assert(extraRhs.length == 1)
      Assignment(extraRhs.head, e).setPos(e.pos)
  }

  private def singleNonIdentIdx(es: Seq[Expr]): Int = {
    val i1 = es.indexWhere(e => !e.isInstanceOf[Ident])
    if(i1 == -1) -1
    else {
      val i2 = es.lastIndexWhere(e => !e.isInstanceOf[Ident])
      if(i2 == i1) i1 else -2
    }
  }

  private def createCurriedDef(ls: Symbol, rs: Symbol, idx: Int, rhs: Boolean): Symbol = {
    val curryId = Ident(s"${ls.id}$$${if(rhs) "ac" else "nc"}$$${rs.id}")
    globalSymbols.get(curryId.s) match {
      case Some(sym) =>
        if(sym.matchContinuationPort != idx) sys.error("Port mismatch in curried ${ls.id} -> ${rs.id} match in $creator")
        sym
      case None =>
        if(ls.hasPayload && rs.hasPayload)
          sys.error("Implementation limitation: Curried definitions cannot have payload on both sides")
        val curriedPtp = if(ls.hasPayload) ls.payloadType else rs.payloadType
        val emb1 = if(ls.hasPayload) Some(Ident("$l")) else None
        val emb2 = if(rs.hasPayload) Some(Ident("$r")) else None
        val sym = globalSymbols.define(curryId.s, isCons = true, arity = ls.arity + rs.arity - 1, payloadType = curriedPtp, matchContinuationPort = idx)
        val largs = (0 until ls.callArity).map(i => Ident(s"$$l$i"))
        val rargs = (0 until rs.callArity).map(i => Ident(s"$$r$i"))
        val (keepArgs, splitArgs) = if(rhs) (rargs, largs) else (largs, rargs)
        val curryArgs = keepArgs ++ splitArgs.zipWithIndex.filter(_._2 != idx).map(_._1)
        addDerivedRules(defaultDerive.map(Ident(_)), curryId)
        val fwd = Assignment(Apply(curryId, emb1.orElse(emb2), curryArgs), splitArgs(idx))
        addChecked(new CheckedMatchRule(Seq(Branch(None, Nil, Seq(fwd))), ls.id, largs, rs.id, rargs, emb1, emb2))
        sym
    }
  }

  private def addChecked(impl: CheckedRule): Unit = {
    val key = if(impl.name1 <= impl.name2) (impl.name1, impl.name2) else (impl.name2, impl.name1)
    if(checkedRules.contains(key)) sys.error(s"Duplicate rule ${impl.name1} . ${impl.name2}")
    checkedRules.put(key, impl)
  }

  private def addMatchRule(m: Match): Unit = {
    val on2 = m.on match {
      // complete lhs assignment for raw match rules (already completed for def rules):
      case e: Apply =>
        val s = globalSymbols(e.target.s)
        if(s.isDef) {
          assert(e.args.length == s.callArity)
          Assignment(e, Tuple((1 to s.returnArity).map(i => Ident(s"$$ret$i").setPos(e.pos))).setPos(e.pos)).setPos(e.pos)
        } else e
      case e => e
    }
    val unnest = new Normalize(globalSymbols)
    val inlined = unnest.toInline(unnest(Seq(on2)).map(unnest.toConsOrder))
    //inlined.foreach(e => println(e.show))
    inlined match {
      case Seq(Assignment(ApplyCons(_, ls, lemb, largs: Seq[Expr]), ApplyCons(_, rs, remb, rargs))) =>
        val compl = if(ls.isDef) largs.takeRight(ls.returnArity) else Nil
        val connected = m.reduced.map { r =>
          r.copy(reduced = r.reduced.init :+ connectLastStatement(r.reduced.last, compl.asInstanceOf[Seq[Ident]]))
        }
        addMatchRule(ls, lemb, largs, rs, remb, rargs, connected, m.show)
      case _ => sys.error(s"Invalid rule: ${m.show}")
    }
  }

  private def addMatchRule(ls: Symbol, lemb: Option[EmbeddedExpr], largs: Seq[Expr], rs: Symbol, remb: Option[EmbeddedExpr], rargs: Seq[Expr], red: Seq[Branch], creator: => String): Unit = {
    //println(s"addMatchRule($ls${lemb.map(e => s"[${e.show}]").getOrElse("")}(${largs.map(_.show).mkString(", ")}) = $rs${remb.map(e => s"[${e.show}]").getOrElse("")}(${rargs.map(_.show).mkString(", ")}) => ${embRed.map(e => s"[${e.show}]").mkString(", ")}, ${reduced.map(_.show).mkString(", ")})")
    largs.indexWhere(e => !e.isInstanceOf[Ident]) match {
      case -1 =>
        singleNonIdentIdx(rargs) match {
          case -2 => sys.error(s"Only one nested match allowed in $creator")
          case -1 =>
            addChecked(new CheckedMatchRule(red, ls.id,
              largs.asInstanceOf[Seq[Ident]], rs.id, rargs.asInstanceOf[Seq[Ident]],
              lemb.map(_.asInstanceOf[Ident]), remb.map(_.asInstanceOf[Ident])))
          case idx =>
            val currySym = createCurriedDef(ls, rs, idx, false)
            val ApplyCons(_, crs, cemb, crargs) = rargs(idx)
            val clargs = largs ++ rargs.zipWithIndex.filter(_._2 != idx).map(_._1.asInstanceOf[Ident])
            addMatchRule(currySym, lemb.orElse(remb), clargs, crs, cemb, crargs, red, creator)
        }
      case idx =>
        val currySym = createCurriedDef(ls, rs, idx, true)
        val ApplyCons(_, cls, cemb, clargs) = largs(idx)
        val crargs = rargs ++ largs.zipWithIndex.filter(_._2 != idx).map(_._1.asInstanceOf[Ident])
        addMatchRule(currySym, lemb.orElse(remb), crargs, cls, cemb, clargs, red, creator)
    }
  }

  def createMTInterpreter(numThreads: Int, compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : mt.Interpreter =
    new mt.Interpreter(globalSymbols, checkedRules.values, numThreads, compile, debugLog, debugBytecode, collectStats)

  def createST2Interpreter(compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : st2.Interpreter =
    new st2.Interpreter(globalSymbols, checkedRules.values, compile, debugLog, debugBytecode, collectStats)

  def createST3Interpreter(compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : st3.Interpreter =
    new st3.Interpreter(globalSymbols, checkedRules.values, compile, debugLog, debugBytecode, collectStats)

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
    data.foreach(inter.scope.addData(_, globalSymbols))
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
  private def mk(): Ident = { lastTmp += 1; Ident(s"$$u${lastTmp}") }

  def apply(exprs: Seq[Expr]): Seq[Expr] = {
    val assigned = mutable.HashSet.empty[Ident]
    val buf = mutable.ArrayBuffer.empty[Expr]
    def expandWildcards(e: Expr, wild: Ident): Expr = e match {
      case Assignment(ls, rs) =>
        val wild2 = mk()
        val ass2 = Assignment(expandWildcards(ls, wild2), expandWildcards(rs, wild2)).setPos(e.pos)
        if(assigned.contains(wild2)) { reorder(unnest(ass2, false)); wild2 }
        else ass2
      case Tuple(es) => Tuple(es.map(expandWildcards(_, wild))).setPos(e.pos)
      case Apply(t, emb, args) => Apply(t, emb, args.map(expandWildcards(_, wild))).setPos(e.pos)
      case Wildcard() =>
        if(assigned.contains(wild)) sys.error(s"Duplicate wildcard in assignment")
        assigned += wild
        wild
      case e: Ident => e
    }
    def unnest(e: Expr, nested: Boolean): Expr = e match {
      case Assignment(ls, rs) =>
        if(nested) sys.error("Unexpected nested assignment without wilcard")
        else Assignment(unnest(ls, false), unnest(rs, false)).setPos(e.pos)
      case Tuple(es) => Tuple(es.map(unnest(_, true))).setPos(e.pos)
      case IdentOrAp(s, emb, args) =>
        val symO = globals.get(s)
        if(symO.exists(_.isCons) || args.nonEmpty) {
          val ap = Apply(Ident(s).setPos(e.pos), emb, args.map(unnest(_, true))).setPos(e.pos)
          if(nested) {
            val v = mk()
            reorder(Assignment(v, ap).setPos(e.pos))
            v
          } else ap
        } else Ident(s).setPos(e.pos)
    }
    def reorder(e: Expr): Unit = e match {
      case Assignment(ls: Apply, rs: Apply) =>
        val sym1 = globals(ls.target.s)
        val sym2 = globals(rs.target.s)
        if(sym1.returnArity != sym2.returnArity) sys.error(s"Invalid assignments with different arities: $e")
        if(sym1.returnArity == 1) {
          val v = mk()
          buf += Assignment(v, ls).setPos(ls.pos)
          buf += Assignment(v, rs).setPos(rs.pos)
        } else {
          val vs = (0 until sym1.returnArity).map(_ => mk())
          buf += Assignment(Tuple(vs).setPos(ls.pos), ls).setPos(ls.pos)
          buf += Assignment(Tuple(vs).setPos(rs.pos), rs).setPos(rs.pos)
        }
      case Assignment(ls: Apply, rs) => reorder(Assignment(rs, ls).setPos(e.pos))
      case Assignment(Tuple(ls), Tuple(rs)) =>
        ls.zip(rs).foreach { case (l, r) => reorder(Assignment(l, r).setPos(e.pos)) }
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
  def toConsOrder(e: Expr): Expr = e match {
    case Assignment(id  @ IdentOrTuple(es), a @ Apply(t, emb, args)) =>
      val s = globals(t.s)
      if(!s.isDef) Assignment(id, ApplyCons(t, s, emb, args).setPos(a.pos)).setPos(e.pos) else Assignment(args.head, ApplyCons(t, s, emb, args.tail ++ es).setPos(a.pos)).setPos(e.pos)
    case Apply(t, emb, args) =>
      val s = globals(t.s)
      if(!s.isDef) ApplyCons(t, s, emb, args).setPos(e.pos) else Assignment(args.head, ApplyCons(t, s, emb, args.tail).setPos(e.pos))
    case e => e
  }

  // convert from cons-order ANF back to inlined expressions
  def toInline(es: Seq[Expr]): Seq[Expr] = {
    if(es.isEmpty) es
    else {
      val vars = mutable.HashMap.from(es.init.map { case a: Assignment => (a.lhs, a) })
      def f(e: Expr): Expr = e match {
        case e: Ident => vars.remove(e).map { a => f(a.rhs) }.getOrElse(e)
        case e: Tuple => vars.remove(e).map { a => f(a.rhs) }.getOrElse(e)
        case ApplyCons(target, tsym, emb, args) => ApplyCons(target, tsym, emb, args.map(f)).setPos(e.pos)
        case Assignment(l, r) => Assignment(f(r), f(l)).setPos(e.pos)
      }
      val e2 = f(es.last)
      (vars.valuesIterator ++ Iterator.single(e2)).toSeq
    }
  }
}
