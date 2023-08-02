package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable

sealed trait CheckedRule {
  def show: String
  def sym1: Symbol
  def sym2: Symbol
}

class DerivedRule(val sym1: Symbol, val sym2: Symbol) extends CheckedRule {
  def show = s"$sym1 . $sym2 = <derived>"
}

class CheckedMatchRule(val reduction: Vector[Branch], val sym1: Symbol, val args1: Seq[Ident], val sym2: Symbol, val args2: Seq[Ident],
    val emb1: Option[Ident], val emb2: Option[Ident]) extends CheckedRule {
  def show: String = {
    def on(n: Symbol, e: Option[Ident], as: Seq[Ident]): String =
      s"$n${e.map(s => s"[${s.show}]").getOrElse("")}(${as.map(_.s).mkString(", ")})"
    s"match ${on(sym1, emb1, args1)} = ${on(sym2, emb2, args2)} ${Branch.show(reduction)}"
  }
}

trait BaseInterpreter {
  def scope: Analyzer[_]
  def reduce(): Int
}

class Compiler(val unit: CompilationUnit, val global: Global = new Global) {
  import global._

  private[this] val prepare = new Prepare(global)
  private[this] val normalize = new Normalize(global)
  private[this] val checkedRules = mutable.Map.empty[(String, String), CheckedRule]

  if(addEraseDup) {
    val erase = globalSymbols.define("erase", isCons = true, isDef = true, returnArity = 0)
    val dup = globalSymbols.define("dup", isCons = true, isDef = true, arity = 2, returnArity = 2)
    addChecked(new DerivedRule(erase, erase))
    addChecked(new DerivedRule(erase, dup))
    addChecked(new DerivedRule(dup, dup))
  }

  prepare.apply(unit)

  val unit2 = (new Transform {
    private[this] def wildcardCount(e: Expr): Int = e match {
      case _: Wildcard => 1
      case e: Apply => e.args.iterator.map(wildcardCount).sum
      case _ => 0
    }
    private[this] def returnArity(e: Expr): Int = e match {
      case e: Apply => e.target.sym.returnArity
      case Assignment(lhs, rhs) => wildcardCount(lhs) + wildcardCount(rhs)
      case _ => 0
    }
    override def apply(n: Statement): Statement = n match {
      case n: Match => apply(n): Match
      case n => n
    }
    override def apply(m: Match): Match = returnArity(m.on) match {
      case 0 => m
      case n =>
        val p = m.on.pos
        m.copy(on = Assignment(m.on, Tuple((1 to n).map(i => mkLocalId(s"$$ret$i").setPos(p)).toVector).setPos(p)).setPos(p)).setPos(m.pos)
    }
  })(unit)

  private[this] lazy val defaultDeriveSyms =
    defaultDerive.iterator.map(globalSymbols.get).filter(_.exists(_.isCons)).map(_.get).toSeq

  private[this] val data = mutable.ArrayBuffer.empty[Let]
  unit2.statements.foreach {
    case c: Cons =>
      addDerivedRules(c.der.map(_.map(_.sym)).getOrElse(defaultDeriveSyms), c.name.sym, c.name.pos)
    case d: Def =>
      d.rules.foreach { r =>
        val dret = Tuple(d.ret).setPos(d.pos)
        addMatchRule(Match(Assignment(Apply(d.name, d.embeddedId, r.on ++ d.args.drop(r.on.length)).setPos(d.pos), dret).setPos(r.pos), r.reduced).setPos(r.pos))
      }
      addChecked(new DerivedRule(globalSymbols("erase"), d.name.sym))
      if(d.name.s != "dup" && d.name.s != "erase")
        addChecked(new DerivedRule(globalSymbols("dup"), d.name.sym))
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

  private def addDerivedRules(syms1: Seq[Symbol], sym2: Symbol, pos: Position): Unit = {
    syms1.foreach { sym =>
      if(sym.id == "erase" || sym.id == "dup") addChecked(new DerivedRule(sym, sym2))
      else error(s"Don't know how to derive '$sym'", pos)
    }
  }

  private def connectLastStatement(e: Expr, extraRhs: Vector[Ident]): Expr = e match {
    case e: Assignment => e
    case e: Tuple =>
      assert(e.exprs.length == extraRhs.length)
      Assignment(Tuple(extraRhs).setPos(extraRhs.head.pos), e).setPos(extraRhs.head.pos)
    case e: Apply =>
      val sym = globalSymbols(e.target.s)
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
    globalSymbols.get(curryId) match {
      case Some(sym) =>
        if(sym.matchContinuationPort != idx) sys.error("Port mismatch in curried ${ls.id} -> ${rs.id} match in $creator")
        curryId.sym = sym
      case None =>
        if(ls.hasPayload && rs.hasPayload)
          sys.error("Implementation limitation: Curried definitions cannot have payload on both sides")
        else {
          val curriedPtp = if(ls.hasPayload) ls.payloadType else rs.payloadType
          val emb1 = if(ls.hasPayload) Some(Ident("$l")) else None
          val emb2 = if(rs.hasPayload) Some(Ident("$r")) else None
          curryId.sym = globalSymbols.define(curryId.s, isCons = true, arity = ls.arity + rs.arity - 1, payloadType = curriedPtp, matchContinuationPort = idx)
          val largs = (0 until ls.callArity).map(i => Ident(s"$$l$i")).toVector
          val rargs = (0 until rs.callArity).map(i => Ident(s"$$r$i")).toVector
          val (keepArgs, splitArgs) = if(rhs) (rargs, largs) else (largs, rargs)
          val curryArgs = keepArgs ++ splitArgs.zipWithIndex.filter(_._2 != idx).map(_._1)
          addDerivedRules(defaultDeriveSyms, curryId.sym, Position.unknown)
          val fwd = Assignment(Apply(curryId, emb1.orElse(emb2), curryArgs), splitArgs(idx))
          addChecked(new CheckedMatchRule(Vector(Branch(None, Vector.empty, Vector(fwd))), ls, largs, rs, rargs, emb1, emb2))
        }
    }
    curryId.sym
  }

  private def addChecked(impl: CheckedRule): Unit = {
    val key = if(impl.sym1.id <= impl.sym2.id) (impl.sym1.id, impl.sym2.id) else (impl.sym2.id, impl.sym1.id)
    if(checkedRules.contains(key)) sys.error(s"Duplicate rule ${impl.sym1.id} . ${impl.sym2.id}")
    checkedRules.put(key, impl)
  }

  private def addMatchRule(m: Match): Unit = {
    val inlined = normalize.toInline(normalize.toANF(Seq(m.on)).map(normalize.toConsOrder))
    inlined match {
      case Seq(Assignment(ApplyCons(lid, lemb, largs: Seq[Expr]), ApplyCons(rid, remb, rargs))) =>
        val compl = if(lid.sym.isDef) largs.takeRight(lid.sym.returnArity) else Vector.empty
        val connected = m.reduced.map { r =>
          r.copy(reduced = r.reduced.init :+ connectLastStatement(r.reduced.last, compl.asInstanceOf[Vector[Ident]]))
        }
        addMatchRule(lid.sym, lemb, largs, rid.sym, remb, rargs, connected, m.show)
      case _ => sys.error(s"Invalid rule: ${m.show}")
    }
  }

  private def addMatchRule(ls: Symbol, lemb: Option[EmbeddedExpr], largs: Seq[Expr], rs: Symbol, remb: Option[EmbeddedExpr], rargs: Seq[Expr], red: Vector[Branch], creator: => String): Unit = {
    //println(s"addMatchRule($ls${lemb.map(e => s"[${e.show}]").getOrElse("")}(${largs.map(_.show).mkString(", ")}) = $rs${remb.map(e => s"[${e.show}]").getOrElse("")}(${rargs.map(_.show).mkString(", ")}) => ${embRed.map(e => s"[${e.show}]").mkString(", ")}, ${reduced.map(_.show).mkString(", ")})")
    largs.indexWhere(e => !e.isInstanceOf[Ident]) match {
      case -1 =>
        singleNonIdentIdx(rargs) match {
          case -2 => sys.error(s"Only one nested match allowed in $creator")
          case -1 =>
            addChecked(new CheckedMatchRule(red, ls,
              largs.asInstanceOf[Seq[Ident]], rs, rargs.asInstanceOf[Seq[Ident]],
              lemb.map(_.asInstanceOf[Ident]), remb.map(_.asInstanceOf[Ident])))
          case idx =>
            val currySym = createCurriedDef(ls, rs, idx, false)
            val ApplyCons(cid, cemb, crargs) = rargs(idx)
            val clargs = largs ++ rargs.zipWithIndex.filter(_._2 != idx).map(_._1.asInstanceOf[Ident])
            addMatchRule(currySym, lemb.orElse(remb), clargs, cid.sym, cemb, crargs, red, creator)
        }
      case idx =>
        val currySym = createCurriedDef(ls, rs, idx, true)
        val ApplyCons(cid, cemb, clargs) = largs(idx)
        val crargs = rargs ++ largs.zipWithIndex.filter(_._2 != idx).map(_._1.asInstanceOf[Ident])
        addMatchRule(currySym, lemb.orElse(remb), crargs, cid.sym, cemb, clargs, red, creator)
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

  def setDataIn(inter: BaseInterpreter): Unit = {
    inter.scope.clear()
    data.foreach(inter.scope.addData(_, globalSymbols))
  }
}
