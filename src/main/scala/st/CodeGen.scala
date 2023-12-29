package de.szeiger.interact.st

import de.szeiger.interact.codegen.{AbstractCodeGen, LocalClassLoader, SymbolIdLookup}
import de.szeiger.interact.{BranchPlan, CellIdx, Connection, FreeIdx, GenericRulePlan, Idx, InitialPlan, RuleKey, RulePlan}
import de.szeiger.interact.ast.Symbol
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

import scala.collection.mutable

class CodeGen(genPackage: String, logGenerated: Boolean, collectStats: Boolean)
  extends AbstractCodeGen[RuleImpl]("de/szeiger/interact/st", genPackage, logGenerated) {

  private val MAX_SPEC_CELL = 2
  private val ptwT = tp.c(s"$interpreterPackage/PerThreadWorker")
  private val cellT = tp.c(s"$interpreterPackage/Cell")
  private val cellNT = tp.c(s"$interpreterPackage/CellNV")
  private val cellSpecTs = (0 to MAX_SPEC_CELL).map(i => tp.c(s"$interpreterPackage/Cell${i}V"))
  private val ri_reduce = riT.method("reduce", tp.m(cellT, cellT, ptwT).V)
  private val cell_reduce = cellT.method("reduce", tp.m(cellT, ptwT).V)
  private val cell_symId = cellT.method("symId", tp.m().I)
  private val cell_auxCell = cellT.method("auxCell", tp.m(tp.I)(cellT))
  private val cell_auxPort = cellT.method("auxPort", tp.m(tp.I)(tp.I))
  private val cell_setAux = cellT.method("setAux", tp.m(tp.I, cellT, tp.I).V)
  private val cell_acell = (0 to MAX_SPEC_CELL).map { a =>
    (0 until a).map(p => cellSpecTs(a).method(s"acell$p", tp.m()(cellT)))
  }
  private val cell_aport = (0 to MAX_SPEC_CELL).map { a =>
    (0 until a).map(p => cellSpecTs(a).method(s"aport$p", tp.m()(tp.I)))
  }
  private val cell_acellSetter = (0 to MAX_SPEC_CELL).map { a =>
    (0 until a).map(p => cellSpecTs(a).method(s"acell${p}_$$eq", tp.m(cellT).V))
  }
  private val cell_aportSetter = (0 to MAX_SPEC_CELL).map { a =>
    (0 until a).map(p => cellSpecTs(a).method(s"aport${p}_$$eq", tp.m(tp.I).V))
  }
  private val ptw_createCut = ptwT.method("createCut", tp.m(cellT, cellT).V)
  private val ptw_recordStats = ptwT.method("recordStats", tp.m(tp.I, tp.I).V)
  private val ptw_irreducible = ptwT.method("irreducible", tp.m(cellT, cellT).V)
  private val ptw_cutCacheCells = ptwT.method("cutCacheCells", tp.m()(cellT.a))
  private val ptw_cutCachePorts = ptwT.method("cutCachePorts", tp.m()(tp.I.a))
  private val new_CellN_II = cellNT.constr(tp.m(tp.I, tp.I).V)
  private val new_CellSpec = cellSpecTs.zipWithIndex.map { case (t, a) =>
    val params = Seq(tp.I) ++ (0 until a).flatMap(_ => Seq(cellT, tp.I))
    t.constr(tp.m(params: _*).V)
  }
  private def ruleT_static_reduce(sym1: Symbol, sym2: Symbol) =
    tp.c(s"$genPackage/Rule_${encodeName(sym1)}$$_${encodeName(sym2)}").method("static_reduce", tp.m(concreteCellTFor(sym1), concreteCellTFor(sym2), ptwT).V)
  private def initialRuleT_static_reduce(idx: Int) =
    tp.c(s"$genPackage/InitialRule_$idx").method("static_reduce", tp.m(cellT, cellT, ptwT).V)

  private def interfaceT(sym: Symbol) = tp.i(s"$genPackage/I_${encodeName(sym)}")
  private def interfaceMethod(sym: Symbol) = interfaceT(sym).method(s"reduce_${encodeName(sym)}", tp.m(concreteCellTFor(sym), ptwT).V)
  private def genericConstrFor(sym: Symbol) = if(sym.arity <= MAX_SPEC_CELL) new_CellSpec(sym.arity) else new_CellN_II
  private def concreteCellTFor(sym: Symbol) = if(sym.isDefined) tp.c(s"$genPackage/C_${encodeName(sym)}") else cellT
  private def concreteConstrFor(sym: Symbol) = concreteCellTFor(sym).constr(genericConstrFor(sym).desc)

  def compileInitial(rule: InitialPlan, cl: LocalClassLoader, lookup: SymbolIdLookup, initialIndex: Int): RuleImpl = {
    val staticMR = initialRuleT_static_reduce(initialIndex)
    val ric = new ClassDSL(Acc.PUBLIC | Acc.FINAL, staticMR.owner.className, riT)
    ric.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(ric, lookup, rule, staticMR)
    implementReduce(ric, 0, None, None, staticMR)
    addClass(cl, ric)
    cl.loadClass(ric.javaName).getDeclaredConstructor().newInstance().asInstanceOf[RuleImpl]
  }

  def compileRule(rule: RulePlan, cl: LocalClassLoader, lookup: SymbolIdLookup): RuleImpl = {
    val staticMR = ruleT_static_reduce(rule.sym1, rule.sym2)
    val ric = new ClassDSL(Acc.PUBLIC | Acc.FINAL, staticMR.owner.className, riT)
    ric.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(ric, lookup, rule, staticMR)
    implementReduce(ric, lookup.getSymbolId(rule.sym1.id), Some(concreteCellTFor(rule.sym1)), Some(concreteCellTFor(rule.sym2)), staticMR)
    addClass(cl, ric)
    cl.loadClass(ric.javaName).getDeclaredConstructor().newInstance().asInstanceOf[RuleImpl]
  }

  private def findReuse(rule: GenericRulePlan, branch: BranchPlan): (Int, Int, Set[Connection]) = {
    // If cell(cellIdx) replaces rhs/lhs, how many connections stay the same?
    def countReuseConnections(cellIdx: Int, rhs: Boolean): Int =
      reuseSkip(cellIdx, rhs).length
    // Find connections to skip for reuse
    def reuseSkip(cellIdx: Int, rhs: Boolean): IndexedSeq[Connection] =
      (0 until branch.cells(cellIdx).arity).flatMap { p =>
        val ci = new CellIdx(cellIdx, p)
        branch.wireConnsDistinct.collect {
          case c @ Connection(FreeIdx(rhs2, fi2), ci2) if ci2 == ci && rhs2 == rhs && fi2 == p => c
          case c @ Connection(ci2, FreeIdx(rhs2, fi2)) if ci2 == ci && rhs2 == rhs && fi2 == p => c
        }
      }
    // Find cellIdx/quality of best reuse candidate for rhs/lhs
    def bestReuse(candidates: Vector[(Symbol, Int)], rhs: Boolean): Option[(Int, Int)] =
      candidates.map { case (s, i) => (i, countReuseConnections(i, rhs)) }
        .sortBy { case (i, q) => -q }.headOption
    // Find sym/cellIdx of cells with same symbol as rhs/lhs
    def reuseCandidates(rhs: Boolean): Vector[(Symbol, Int)] =
      branch.cells.zipWithIndex.filter { case (sym, _) => sym == rule.symFor(rhs) }
    // Find best reuse combination for both sides
    def bestReuse2: (Option[(Int, Int)], Option[(Int, Int)], Set[Connection]) = {
      var cand1 = reuseCandidates(false)
      var cand2 = reuseCandidates(true)
      var best1 = bestReuse(cand1, false)
      var best2 = bestReuse(cand2, true)
      (best1, best2) match {
        case (Some((ci1, q1)), Some((ci2, q2))) if ci1 == ci2 =>
          if(q1 >= q2) { // redo best2
            cand2 = cand2.filter { case (s, i) => i != ci1 }
            best2 = bestReuse(cand2, true)
          } else { // redo best1
            cand1 = cand1.filter { case (s, i) => i != ci2 }
            best1 = bestReuse(cand1, false)
          }
        case _ =>
      }
      val skipConn1 = best1.iterator.flatMap { case (ci, _) => reuseSkip(ci, false) }
      val skipConn2 = best2.iterator.flatMap { case (ci, _) => reuseSkip(ci, true) }
      (best1, best2, (skipConn1 ++ skipConn2).toSet)
    }

    val (r1, r2, skip) = bestReuse2
    (r1.map(_._1).getOrElse(-1), r2.map(_._1).getOrElse(-1), skip)
  }

  private def implementReduce(c: ClassDSL, sid1: Int, cast1: Option[Owner], cast2: Option[Owner], staticMR: MethodRef): Unit = {
    val m = c.method(Acc.PUBLIC | Acc.FINAL, ri_reduce.name, ri_reduce.desc)
    val c1 = m.param("c1", cellT, Acc.FINAL)
    val c2 = m.param("c2", cellT, Acc.FINAL)
    val ptw = m.param("ptw", ptwT, Acc.FINAL)
    m.aload(c1).invokevirtual(cell_symId).iconst(sid1)
    m.ifThenElseI_== {
      m.aload(c1)
      cast1.foreach(m.checkcast)
      m.aload(c2)
      cast2.foreach(m.checkcast)
    } {
      m.aload(c2)
      cast1.foreach(m.checkcast)
      m.aload(c1)
      cast2.foreach(m.checkcast)
    }
    m.aload(ptw).invokestatic(staticMR).return_
  }

  private def implementStaticReduce(c: ClassDSL, lookup: SymbolIdLookup, rule: GenericRulePlan, mref: MethodRef): Unit = {
    assert(rule.branches.length == 1)
    val isInitial = rule.isInstanceOf[InitialPlan]
    val branch = rule.branches.head
    var cellAllocations = 0
    val (reuse1, reuse2, skipConns) = findReuse(rule, branch)
    //val (reuse1, reuse2, skipConns) = (-1, -1, Set.empty[Connection])
    val conns = (branch.wireConnsDistinct ++ branch.internalConnsDistinct).filterNot(skipConns.contains)
    def isReuse(cellIdx: Int): Boolean = cellIdx == reuse1 || cellIdx == reuse2
    def reuseAny = reuse1 != -1 || reuse2 != -1
    val m = c.method(Acc.PUBLIC | Acc.STATIC, mref.name, mref.desc)
    val cLeft = m.param("cLeft", concreteCellTFor(rule.sym1), Acc.FINAL)
    val cRight = m.param("cRight", concreteCellTFor(rule.sym2), Acc.FINAL)
    val ptw = m.param("ptw", ptwT, Acc.FINAL)

    // Helper methods
    def getAuxCell(a: Int, p: Int): m.type =
      if(a < cell_acell.length && !isInitial) m.invokevirtual(cell_acell(a)(p))
      else m.iconst(p).invokevirtual(cell_auxCell)
    def getAuxPort(a: Int, p: Int): m.type =
      if(a < cell_aport.length && !isInitial) m.invokevirtual(cell_aport(a)(p))
      else m.iconst(p).invokevirtual(cell_auxPort)
    def setAux(a: Int, p: Int, setPort: Boolean = true)(loadC2: => Unit)(loadP2: => Unit): m.type = {
      if(a < cell_acell.length) {
        if(setPort) {
          m.dup
          loadP2; m.invokevirtual(cell_aportSetter(a)(p))
        }
        loadC2; m.invokevirtual(cell_acellSetter(a)(p))
      }
      else {
        m.iconst(p) ; loadC2 ; loadP2
        m.invokevirtual(cell_setAux)
      }
    }

    // Copy cached cells (if not skipped due to reuse)
    val skipCache = skipConns.flatMap { case Connection(a, b) => Seq(a, b) }.collect {
      case CellIdx(i, p) if i == reuse1 => (false, p)
      case CellIdx(i, p) if i == reuse2 => (true, p)
    }
    val cccells = m.aload(ptw).invokevirtual(ptw_cutCacheCells).storeLocal("cccells", cellT.a)
    val ccports = m.aload(ptw).invokevirtual(ptw_cutCachePorts).storeLocal("ccports", tp.I.a)
    (0 until rule.arity1).foreach { p =>
      if(!skipCache.contains((false, p))) {
        m.aload(cccells).iconst(p).aload(cLeft); getAuxCell(rule.arity1, p).aastore
        m.aload(ccports).iconst(p).aload(cLeft); getAuxPort(rule.arity1, p).iastore
      }
    }
    (0 until rule.arity2).foreach { p =>
      if(!skipCache.contains((true, p))) {
        m.aload(cccells).iconst(p + rule.arity1).aload(cRight); getAuxCell(rule.arity2, p).aastore
        m.aload(ccports).iconst(p + rule.arity1).aload(cRight); getAuxPort(rule.arity2, p).iastore
      }
    }

    // Create new cells & update symbols of reused cells
    val cells = mutable.ArraySeq.fill[VarIdx](branch.cells.length)(VarIdx.none)
    for(idx <- cells.indices) {
      cells(idx) = branch.cells(idx) match {
        case _ if idx == reuse1 => cLeft
        case _ if idx == reuse2 => cRight
        case sym =>
          val constr = concreteConstrFor(sym)
          cellAllocations += 1
          m.newInitDup(constr) {
            m.iconst(lookup.getSymbolId(sym.id))
            if(sym.arity <= MAX_SPEC_CELL) {
              branch.cellConns(idx).tail.foreach {
                case CellIdx(ci, p) =>
                  if(cells(ci) == VarIdx.none) m.aconst_null else m.aload(cells(ci))
                  m.iconst(p)
                case f: FreeIdx => ldBoth(f)
              }
            } else m.iconst(sym.arity)
          }
          m.storeLocal(s"c$idx", constr.tpe, Acc.FINAL)
      }
    }

    // Cell accessors
    def ldCell(idx: Idx) = idx match {
      case FreeIdx(rhs, i) => m.aload(cccells).iconst(if(rhs) i + rule.arity1 else i).aaload
      case CellIdx(i, p) => m.aload(cells(i))
    }
    def ldPort(idx: Idx) = idx match {
      case FreeIdx(rhs, i) => m.aload(ccports).iconst(if(rhs) i + rule.arity1 else i).iaload
      case CellIdx(i, p) => m.iconst(p)
    }
    def ldBoth(idx: Idx) = { ldCell(idx); ldPort(idx) }

    // Connect remaining wires
    def connectCF(ct1: CellIdx, ct2: FreeIdx): Unit = {
      val (c1, p1) = (ct1.idx, ct1.port)
      if(isReuse(c1)) {
        m.aload(cells(c1))
        if(p1 >= 0) setAux(branch.cells(c1).arity, p1)(ldCell(ct2))(ldPort(ct2))
      }
      if(p1 < 0) {
        ldPort(ct2).iconst(0).ifThenElseI_>= {
          ldBoth(ct2); ldBoth(ct1).invokevirtual(cell_setAux)
        } {
          m.aload(ptw); ldCell(ct1); ldCell(ct2).invokevirtual(ptw_createCut)
        }
      } else {
        ldPort(ct2).iconst(0).ifThenI_>= {
          ldBoth(ct2); ldBoth(ct1).invokevirtual(cell_setAux)
        }
      }
//      m.aload(c2).aload(cut1).ifThenElseA_== {
//        m.aload(cells(c1)).astore(lhs(p2)._1)
//        m.iconst(p1).istore(lhs(p2)._2)
//      } {
//        m.aload(c2).aload(cut2).ifThenA_== {
//          m.aload(cells(c1)).astore(rhs(p2)._1)
//          m.iconst(p1).istore(rhs(p2)._2)
//        }
//      }
    }
    def connectFF(ct1: FreeIdx, ct2: FreeIdx): Unit = {
      ldPort(ct1).iconst(0).ifThenI_>= {
        ldBoth(ct1); ldBoth(ct2).invokevirtual(cell_setAux)
      }
      ldPort(ct2).iconst(0).ifThenElseI_>= {
        ldBoth(ct2); ldBoth(ct1).invokevirtual(cell_setAux)
      } {
        ldPort(ct1).iconst(0).ifThenI_< {
          m.aload(ptw); ldCell(ct1); ldCell(ct2).invokevirtual(ptw_createCut)
        }
      }
    }
    def connectCC(ct1: CellIdx, ct2: CellIdx): Unit = {
      val (c1, p1) = (ct1.idx, ct1.port)
      val (c2, p2) = (ct2.idx, ct2.port)
      if(c2 >= c1 || isReuse(c1)) {
        m.aload(cells(c1))
        if(p1 >= 0)
          setAux(branch.cells(c1).arity, p1, isReuse(c1))(m.aload(cells(c2)))(m.iconst(p2))
      }
      if(c1 >= c2 || isReuse(c2)) {
        m.aload(cells(c2))
        if(p2 >= 0)
          setAux(branch.cells(c2).arity, p2, isReuse(c2))(m.aload(cells(c1)))(m.iconst(p1))
      }
      if(p1 < 0 && p2 < 0) {
        m.aload(ptw); ldCell(ct1); ldCell(ct2).invokevirtual(ptw_createCut)
      }
    }
    conns.foreach {
      case Connection(i1: FreeIdx, i2: FreeIdx) => connectFF(i1, i2)
      case Connection(i1: FreeIdx, i2: CellIdx) => connectCF(i2, i1)
      case Connection(i1: CellIdx, i2: FreeIdx) => connectCF(i1, i2)
      case Connection(i1: CellIdx, i2: CellIdx) => connectCC(i1, i2)
    }

    if(collectStats)
      m.aload(ptw).iconst(1).iconst(cellAllocations).invokevirtual(ptw_recordStats)
    m.return_

    // statistics
    c.method(Acc.PUBLIC, "cellAllocationCount", tp.m().I).iconst(cellAllocations).ireturn
  }

  def compileInterface(sym: Symbol, cl: LocalClassLoader): Unit = {
    val ifm = interfaceMethod(sym)
    val c = new ClassDSL(Acc.PUBLIC | Acc.INTERFACE, ifm.owner.className)
    c.method(Acc.PUBLIC | Acc.ABSTRACT, ifm.name, ifm.desc)
    addClass(cl, c)
  }

  def compileCons(sym: Symbol, rules: scala.collection.Map[RuleKey, _], cl: LocalClassLoader): Unit = {
    val parentConstr = genericConstrFor(sym)
    val rulePairs = rules.keys.iterator.collect {
      case rk if rk.sym1 == sym => (rk.sym2, rk)
      case rk if rk.sym2 == sym => (rk.sym1, rk)
    }.toMap
    val interfaces = rulePairs.keysIterator.map(s => interfaceT(s).className).toArray.sorted
    val c = new ClassDSL(Acc.PUBLIC | Acc.FINAL, concreteCellTFor(sym).className, parentConstr.tpe, interfaces)

    // copy constructor
    if(sym.arity <= MAX_SPEC_CELL) {
      val params = Seq(tp.I) ++ (0 until sym.arity).flatMap(_ => Seq(cellT, tp.I))
      val m = c.constructor(Acc.PUBLIC, tp.m(params: _*))
      val symId = m.param("symId", tp.I, Acc.FINAL)
      val aux = (0 until sym.arity).map(i => (m.param(s"c$i", cellT), m.param(s"p$i", tp.I)))
      m.aload(m.receiver).iload(symId)
      aux.foreach { case (c, p) => m.aload(c).iload(p) }
      m.invokespecial(parentConstr).return_
    } else {
      val m = c.constructor(Acc.PUBLIC, tp.m(tp.I, tp.I))
      val symId = m.param("symId", tp.I, Acc.FINAL)
      val arity = m.param("arity", tp.I, Acc.FINAL)
      m.aload(m.receiver).iload(symId).iload(arity).invokespecial(parentConstr).return_
    }

    // generic reduce
    {
      val m = c.method(Acc.PUBLIC | Acc.FINAL, cell_reduce.name, cell_reduce.desc)
      val other = m.param("other", cellT, Acc.FINAL)
      val ptw = m.param("ptw", ptwT, Acc.FINAL)
      val ifm = interfaceMethod(sym)
      m.aload(other)
      m.tryCatchGoto(tp.c[ClassCastException]) {
        m.checkcast(ifm.owner)
      } {
        m.pop
        m.aload(ptw).aload(m.receiver).aload(other).invokevirtual(ptw_irreducible)
        m.return_
      }
      m.aload(m.receiver).aload(ptw).invokeinterface(ifm)
      m.return_
    }

    // interface methods
    rulePairs.foreach { case (sym2, rk) =>
      val ifm = interfaceMethod(sym2)
      val m = c.method(Acc.PUBLIC | Acc.FINAL, ifm.name, ifm.desc)
      val other = m.param("other", concreteCellTFor(sym2), Acc.FINAL)
      val ptw = m.param("ptw", ptwT, Acc.FINAL)
      val staticMR = ruleT_static_reduce(rk.sym1, rk.sym2)
      if(rk.sym1 == sym) m.aload(m.receiver).aload(other)
      else m.aload(other).aload(m.receiver)
      m.aload(ptw).invokestatic(staticMR).return_
    }
    addClass(cl, c)
  }
}

/*

interface I_dup {
  def reduce_dup(c: C_dup): Unit
}

interface I_S {
  def reduce_S(c: C_S): Unit
}

class C_dup extends Cell2V, I_S, ... {
  def reduce(c: Cell, ptw: PerThreadWorker): Unit = c.asInstanceOf[I_dup].reduce_dup(this, ptw)
  def reduce_S(c: C_S): Unit = R_dup_S.reduce(this, c)
}

class C_S extends Cell2V, I_dup, ... {
}

*/
