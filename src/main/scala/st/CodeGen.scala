package de.szeiger.interact.st

import de.szeiger.interact.codegen.{AbstractCodeGen, LocalClassLoader, ParSupport}
import de.szeiger.interact.{BackendConfig, BranchPlan, CellIdx, Connection, CreateLabelsComp, EmbArg, FreeIdx, GenericRulePlan, Global, Idx, InitialPlan, IntBox, PayloadAssignment, PayloadComputation, PayloadMethodApplication, PayloadMethodApplicationWithReturn, RefBox, RuleKey, RulePlan}
import de.szeiger.interact.ast.{PayloadType, Symbol, Symbols}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class CodeGen(genPackage: String, classLoader: LocalClassLoader, config: BackendConfig) extends AbstractCodeGen[RuleImpl](config) {

  private val riT = tp.c[RuleImpl]
  private val ptwT = tp.c[PerThreadWorker]
  private val cellT = tp.c[Cell]
  private val intBoxT = tp.i[IntBox]
  private val refBoxT = tp.i[RefBox]
  private val commonCellT = tp.c(s"$genPackage/CommonCell")
  private val cellCacheT = tp.c(s"$genPackage/CellCache")
  private val ri_reduce = riT.method("reduce", tp.m(cellT, cellT, ptwT).V)
  private val cell_reduce = cellT.method("reduce", tp.m(cellT, ptwT).V)
  private val cell_arity = cellT.method("arity", tp.m().I)
  private val cell_auxCell = cellT.method("auxCell", tp.m(tp.I)(cellT))
  private val cell_auxPort = cellT.method("auxPort", tp.m(tp.I).I)
  private val cell_setAux = cellT.method("setAux", tp.m(tp.I, cellT, tp.I).V)
  private val ptw_createCut = ptwT.method("createCut", tp.m(cellT, cellT).V)
  private val ptw_recordStats = ptwT.method("recordStats", tp.m(tp.I, tp.I, tp.I, tp.I).V)
  private val ptw_recordMetric = ptwT.method("recordMetric", tp.m(tp.c[String], tp.I).V)
  private val ptw_irreducible = ptwT.method("irreducible", tp.m(cellT, cellT).V)
  private val intBox_getValue = intBoxT.method("getValue", tp.m().I)
  private val intBox_setValue = intBoxT.method("setValue", tp.m(tp.I).V)
  private val refBox_getValue = refBoxT.method("getValue", tp.m()(tp.c[AnyRef]))
  private val refBox_setValue = refBoxT.method("setValue", tp.m(tp.c[AnyRef]).V)
  private val new_CommonCell = commonCellT.constr(tp.m().V)

  private def ruleT_static_reduce(sym1: Symbol, sym2: Symbol) =
    tp.c(s"$genPackage/Rule_${encodeName(sym1)}$$_${encodeName(sym2)}").method("static_reduce", tp.m(concreteCellTFor(sym1), concreteCellTFor(sym2), ptwT).V)
  private def initialRuleT_static_reduce(idx: Int) =
    tp.c(s"$genPackage/InitialRule_$idx").method("static_reduce", tp.m(cellT, cellT, ptwT).V)
  private def interfaceT(sym: Symbol) = tp.i(s"$genPackage/I_${encodeName(sym)}")
  private def interfaceMethod(sym: Symbol) = interfaceT(sym).method(s"reduce_${encodeName(sym)}", tp.m(concreteCellTFor(sym), ptwT).V)
  private def concreteCellTFor(sym: Symbol) = if(sym.isDefined) tp.c(s"$genPackage/C_${encodeName(sym)}") else cellT
  private def concreteConstrFor(sym: Symbol) = concreteCellTFor(sym).constr(tp.m((0 until sym.arity).flatMap(_ => Seq(cellT, tp.I)): _*).V)
  private def concreteReinitFor(sym: Symbol) = concreteCellTFor(sym).method("reinit", tp.m((0 until sym.arity).flatMap(_ => Seq(cellT, tp.I)): _*).V)
  private def concretePayloadFieldFor(sym: Symbol) = concreteCellTFor(sym).field("value", sym.payloadType match {
    case PayloadType.INT => tp.I
    case _ => tp.c[AnyRef]
  })
  private def cell_acell(sym: Symbol, p: Int) = concreteCellTFor(sym).field(s"acell$p", cellT)
  private def cell_aport(sym: Symbol, p: Int) = concreteCellTFor(sym).field(s"aport$p", tp.I)
  private def cell_singleton(sym: Symbol) = { val tp = concreteCellTFor(sym); tp.field("singleton", tp) }
  private def isSingleton(sym: Symbol) = sym.arity == 0 && sym.payloadType.isEmpty
  private def cellCache_var(sym: Symbol) = cellCacheT.field(s"f_${encodeName(sym)}", concreteCellTFor(sym))
  private def cellCache_get(sym: Symbol) = cellCacheT.method(s"get_${encodeName(sym)}", tp.m()(concreteCellTFor(sym)))
  private def cellCache_set(sym: Symbol) = cellCacheT.method(s"set_${encodeName(sym)}", tp.m(concreteCellTFor(sym)).V)

  private def implementStaticReduce(c: ClassDSL, rule: GenericRulePlan, mref: MethodRef, common: scala.collection.Set[Symbol], rules: scala.collection.Map[RuleKey, RulePlan]): Unit = {
    //assert(rule.branches.length == 1)
    val m = c.method(Acc.PUBLIC | Acc.STATIC, mref.name, mref.desc)
    val cLeftTp = concreteCellTFor(rule.sym1)
    val cRightTp = concreteCellTFor(rule.sym2)
    val cLeft = m.param("cLeft", cLeftTp)
    val cRight = m.param("cRight", cRightTp)
    val ptw = m.param("ptw", ptwT, Acc.FINAL)
    incMetric(s"${c.name}.${m.name}", m, ptw)
    val methodEnd = if(rule.branches.length > 1) m.newLabel else null
    rule.branches.foreach { branch =>
      emitBranchReduce(m: MethodDSL, rule, branch, rule.isInstanceOf[InitialPlan], cLeft, cRight, cLeftTp, cRightTp, ptw, common, rules, methodEnd)
    }
    if(methodEnd != null) m.setLabel(methodEnd)
    m.return_
  }

  private def emitBranchReduce(m: MethodDSL, rule: GenericRulePlan, branch: BranchPlan, isInitial: Boolean,
      cLeft: VarIdx, cRight: VarIdx, cLeftTp: ClassOwner, cRightTp: ClassOwner, ptw: VarIdx,
      common: scala.collection.Set[Symbol], rules: scala.collection.Map[RuleKey, RulePlan],
      methodEnd: Label): Unit = {
    val branchEnd = m.newLabel

    def callPayloadMethod(pc: PayloadMethodApplication)(loadArgs: => Unit): Unit = {
      val mref = MethodRef(pc.jMethod)
      if(pc.isStatic) {
        loadArgs
        m.invokestatic(mref)
      } else {
        m.getstatic(mref.owner.field("MODULE$", mref.owner))
        loadArgs
        m.invoke(mref)
      }
    }

    branch.condition.foreach { case pc: PayloadMethodApplication =>
      def adaptPayloadFromCell(cell: VarIdx, cellTp: Owner, cls: Class[_]): Unit = {
        m.aload(cell)
        if(cls == classOf[Int]) m.invoke(intBox_getValue, cellTp)
        else if(cls == classOf[AnyRef]) m.invoke(refBox_getValue, cellTp)
        else m.invoke(refBox_getValue, cellTp).checkcast(tp.o(cls))
      }
      callPayloadMethod(pc) {
        pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach {
          case (EmbArg.Const(i: Int), _) => m.iconst(i)
          case (EmbArg.Const(s: String), _) => m.ldc(s)
          case (EmbArg.Left, cls) => adaptPayloadFromCell(cLeft, cLeftTp, cls)
          case (EmbArg.Right, cls) => adaptPayloadFromCell(cRight, cRightTp, cls)
        }
      }
      assert(pc.jMethod.getReturnType == classOf[Boolean])
      m.ifeq(branchEnd)
    }

    val (reuse1, reuse2, skipConns) = findReuse(rule, branch)
    val conns = (branch.internalConnsDistinct ++ branch.wireConnsDistinct).filterNot(skipConns.contains)
    def isReuse(cellIdx: CellIdx): Boolean = cellIdx.idx == reuse1 || cellIdx.idx == reuse2
    //val (uniqueConts, uniqueContPoss) = uniqueContinuationsFor(rule, rules)

    //TODO allow local looping over multiple branches
    val loopOn1 = reuse1 != -1 && ((rule.sym1.isDef || reuse2 == -1) || !config.biasForCommonDispatch) && rule.branches.length == 1
    val loopOn2 = reuse2 != -1 && ((rule.sym2.isDef || reuse1 == -1) || !config.biasForCommonDispatch) && rule.branches.length == 1
    val (cont1, cont2, loopStart) = {
      if(loopOn1 || loopOn2) {
        val cont1 = m.aconst_null.storeAnonLocal(concreteCellTFor(rule.sym1))
        val cont2 = m.aconst_null.storeAnonLocal(concreteCellTFor(rule.sym2))
        (cont1, cont2, m.setLabel())
      } else (VarIdx.none, VarIdx.none, null)
    }

    // Create new cells
    val statCellAllocations, statCachedCellReuse = if(config.collectStats) m.iconst(0).storeAnonLocal(tp.I) else VarIdx.none
    var statSingletonUse = 0
    val cells = mutable.ArraySeq.fill[VarIdx](branch.cells.length)(VarIdx.none)
    val cellPortsConnected = mutable.HashSet.empty[CellIdx]
    var cellPortsNotConnected = 0
    for(idx <- optimizeCellCreationOrder(branch.cells.length, branch.internalConnsDistinct)) {
      cells(idx) = branch.cells(idx) match {
        case _ if idx == reuse1 => cLeft
        case _ if idx == reuse2 => cRight
        case sym =>
          val constr = concreteConstrFor(sym)
          if(isSingleton(sym)) {
            m.getstatic(cell_singleton(sym))
            statSingletonUse += 1
          } else {
            def loadParams() = {
              branch.auxConns(idx).zipWithIndex.foreach {
                case (CellIdx(ci, p2), p1) =>
                  if(cells(ci) == VarIdx.none) { m.aconst_null; cellPortsNotConnected += 1 }
                  else { m.aload(cells(ci)); cellPortsConnected += CellIdx(idx, p1) }
                  m.iconst(p2)
                case (f: FreeIdx, _) => ldBoth(f)
              }
            }
            if(isInitial || !config.useCellCache) {
              m.newInitDup(constr)(loadParams())
              if(config.collectStats) m.iinc(statCellAllocations)
            } else {
              m.invokestatic(cellCache_get(sym)).dup.ifNullThenElse {
                m.pop
                m.newInitDup(constr)(loadParams())
                if(config.collectStats) m.iinc(statCellAllocations)
              } {
                m.dup
                loadParams()
                m.invoke(concreteReinitFor(sym))
                if(config.collectStats) m.iinc(statCachedCellReuse)
              }
            }
          }
          m.storeLocal(s"c$idx", constr.tpe)
      }
    }
    //println(s"Connected ${cellPortsConnected.size} of ${cellPortsConnected.size+cellPortsNotConnected} ports")

    // Cell accessors
    def ldCell(idx: Idx) = idx match {
      case FreeIdx(rhs, p) =>
        m.aload(if(rhs) cRight else cLeft)
        if(isInitial) m.iconst(p).invoke(cell_auxCell)
        else m.getfield(cell_acell(if(rhs) rule.sym2 else rule.sym1, p))
      case CellIdx(i, _) => m.aload(cells(i))
    }
    def ldPort(idx: Idx) = idx match {
      case FreeIdx(rhs, p) =>
        m.aload(if(rhs) cRight else cLeft)
        if(isInitial) m.iconst(p).invoke(cell_auxPort)
        else m.getfield(cell_aport(if(rhs) rule.sym2 else rule.sym1, p))
      case CellIdx(_, p) => m.iconst(p)
    }
    def ldBoth(idx: Idx) = { ldCell(idx); ldPort(idx) }

    val reuse1Buffer = Array.fill[VarIdx](rule.arity1*2)(VarIdx.none)
    val reuse2Buffer = Array.fill[VarIdx](rule.arity2*2)(VarIdx.none)
    def setAux(idx: CellIdx, ct2: Idx, setPort: Boolean = true): m.type = {
      val sym = branch.cells(idx.idx)
      if(idx.idx == reuse1) {
        ldCell(ct2)
        reuse1Buffer(idx.port*2) = m.storeAnonLocal(cellT)
        if(setPort) {
          ldPort(ct2)
          reuse1Buffer(idx.port*2+1) = m.storeAnonLocal(tp.I)
        }
      } else if(idx.idx == reuse2) {
        ldCell(ct2)
        reuse2Buffer(idx.port*2) = m.storeAnonLocal(cellT)
        if(setPort) {
          ldPort(ct2)
          reuse2Buffer(idx.port*2+1) = m.storeAnonLocal(tp.I)
        }
      } else {
        m.aload(cells(idx.idx))
        if(setPort) m.dup
        ldCell(ct2).putfield(cell_acell(sym, idx.port))
        if(setPort) ldPort(ct2).putfield(cell_aport(sym, idx.port))
      }
      m
    }

    // Always cache input payloads to support cell reuse (we need to read them anyway)
    val (cachedPayload1, cachedPayload2) = {
      def cache(cell: VarIdx, pt: PayloadType, boxTp: Owner): VarIdx = pt match {
        case PayloadType.VOID => VarIdx.none
        case PayloadType.INT => m.aload(cell).invoke(intBox_getValue.on(boxTp)).storeAnonLocal(tp.I)
        case _ => m.aload(cell).invoke(refBox_getValue.on(boxTp)).storeAnonLocal(tp.c[AnyRef])
      }
      (cache(cLeft, rule.sym1.payloadType, cLeftTp), cache(cRight, rule.sym2.payloadType, cRightTp))
    }

    // Compute payloads
    branch.payloadComps.foreach { pc =>
      def adaptCachedPayload(cached: VarIdx, cls: Class[_]): Unit = {
        if(cls == classOf[Int]) m.iload(cached)
        else if(cls == classOf[AnyRef]) m.aload(cached)
        else m.aload(cached).checkcast(tp.o(cls))
      }
      def loadArg(embArg: EmbArg, cls: Class[_]): Unit = embArg match {
        case EmbArg.Const(i: Int) => m.iconst(i)
        case EmbArg.Const(s: String) => m.ldc(s)
        case EmbArg.Left => adaptCachedPayload(cachedPayload1, cls)
        case EmbArg.Right => adaptCachedPayload(cachedPayload2, cls)
        case EmbArg.Cell(idx) => m.aload(cells(idx))
      }
      def setCellValue(embArg: EmbArg.Cell, cls: Class[_]): Unit = {
        val boxTp = concreteCellTFor(branch.cells(embArg.idx))
        m.aload(cells(embArg.idx)).swap
        m.invoke((if(cls == classOf[Int]) intBox_setValue else refBox_setValue).on(boxTp))
      }
      def loadArgs(pc: PayloadMethodApplication): Unit =
        pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach { case (embArg, cls) => loadArg(embArg, cls) }
      pc match {
        case pc: PayloadMethodApplication =>
          assert(pc.jMethod.getReturnType == Void.TYPE)
          callPayloadMethod(pc)(loadArgs(pc))
        case pc: CreateLabelsComp =>
          m.newInitDup(tp.c[AnyRef].constr(tp.m().V))() //TODO use cells as labels instead of creating unnecessary objects
          pc.embArgs.foreach { case EmbArg.Cell(idx) =>
            m.dup.aload(cells(idx)).swap.invoke(refBox_setValue.on(concreteCellTFor(branch.cells(idx))))
          }
          m.pop //TODO skip last dup so we don't need to pop it
        case pc: PayloadAssignment =>
          assert(pc.payloadType.isDefined)
          if(pc.payloadType == PayloadType.INT) {
            loadArg(pc.targetIdx, classOf[IntBox])
            loadArg(pc.sourceIdx, classOf[Int])
            m.invoke(intBox_setValue.on(concreteCellTFor(branch.cells(pc.targetIdx.asInstanceOf[EmbArg.Cell].idx))))
          } else {
            loadArg(pc.targetIdx, classOf[RefBox])
            loadArg(pc.sourceIdx, classOf[AnyRef])
            m.invoke(refBox_setValue.on(concreteCellTFor(branch.cells(pc.targetIdx.asInstanceOf[EmbArg.Cell].idx))))
          }
        case pc: PayloadMethodApplicationWithReturn =>
          callPayloadMethod(pc.method)(loadArgs(pc.method))
          setCellValue(pc.retIndex.asInstanceOf[EmbArg.Cell], pc.method.jMethod.getReturnType)
      }
    }

    def createCut(ct1: Idx, ct2: Idx) = {
      m.aload(ptw);
      (ct1, ct2) match {
        case (_, CellIdx(idx, _)) if common.contains(branch.cells(idx)) => ldCell(ct2); ldCell(ct1)
        case (CellIdx(idx, _), _: FreeIdx) if !common.contains(branch.cells(idx)) => ldCell(ct2); ldCell(ct1)
        case _ => ldCell(ct1); ldCell(ct2)
      }
      m.invoke(ptw_createCut)
    }

    // Connect remaining wires
    def connectCF(ct1: CellIdx, ct2: FreeIdx): Unit = {
      val (c1, p1) = (ct1.idx, ct1.port)
      if(isReuse(ct1) && p1 >= 0)
        setAux(ct1, ct2)
      if(p1 < 0) {
        ldPort(ct2).if0ThenElse_>= {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        } {
          if(ct1.idx == reuse1 && loopOn1) {
            //println(s"Loop detection: ${rule.sym1} <-> ${rule.sym2}; using sym1")
            val dflt, end = m.newLabel
            m.aload(cont1).ifnonnull(dflt)
            ldCell(ct2).instanceof(concreteCellTFor(rule.sym2))
            m.ifeq(dflt)
            ldCell(ct1).astore(cont1)
            ldCell(ct2).checkcast(concreteCellTFor(rule.sym2)).astore(cont2)
            m.goto(end)
            m.setLabel(dflt)
            createCut(ct1, ct2)
            m.setLabel(end)
          } else if(ct1.idx == reuse2 && loopOn2) {
            //println(s"Loop detection: ${rule.sym1} <-> ${rule.sym2}; using sym2")
            val dflt, end = m.newLabel
            m.aload(cont1).ifnonnull(dflt)
            ldCell(ct2).instanceof(concreteCellTFor(rule.sym1))
            m.ifeq(dflt)
            ldCell(ct1).astore(cont2)
            ldCell(ct2).checkcast(concreteCellTFor(rule.sym1)).astore(cont1)
            m.goto(end)
            m.setLabel(dflt)
            createCut(ct1, ct2)
            m.setLabel(end)
          } else createCut(ct1, ct2)
        }
      } else {
        ldPort(ct2).if0Then_>= {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        }
      }
    }
    def connectFF(ct1: FreeIdx, ct2: FreeIdx): Unit = {
      ldPort(ct1).if0ThenElse_>= {
        ldBoth(ct1); ldBoth(ct2).invoke(cell_setAux)
        ldPort(ct2).if0Then_>= {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        }
      } {
        ldPort(ct2).if0ThenElse_>= {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        } {
          createCut(ct1, ct2)
        }
      }
    }
    def connectCC(ct1: CellIdx, ct2: CellIdx): Unit = {
      val (c1, p1) = (ct1.idx, ct1.port)
      val (c2, p2) = (ct2.idx, ct2.port)
      if(p1 >= 0 && !cellPortsConnected.contains(ct1))
        setAux(ct1, ct2, isReuse(ct1))
      if(p2 >= 0 && !cellPortsConnected.contains(ct2))
        setAux(ct2, ct1, isReuse(ct2))
      if(p1 < 0 && p2 < 0)
        createCut(ct1, ct2)
    }
    conns.foreach {
      case Connection(i1: FreeIdx, i2: FreeIdx) => connectFF(i1, i2)
      case Connection(i1: FreeIdx, i2: CellIdx) => connectCF(i2, i1)
      case Connection(i1: CellIdx, i2: FreeIdx) => connectCF(i1, i2)
      case Connection(i1: CellIdx, i2: CellIdx) => connectCC(i1, i2)
    }

    for(p <- 0 until rule.arity1) {
      if(reuse1Buffer(p*2) != VarIdx.none)
        m.aload(cells(reuse1)).aload(reuse1Buffer(p*2)).putfield(cell_acell(rule.sym1, p))
      if(reuse1Buffer(p*2+1) != VarIdx.none)
        m.aload(cells(reuse1)).iload(reuse1Buffer(p*2+1)).putfield(cell_aport(rule.sym1, p))
    }
    for(p <- 0 until rule.arity2) {
      if(reuse2Buffer(p*2) != VarIdx.none)
        m.aload(cells(reuse2)).aload(reuse2Buffer(p*2)).putfield(cell_acell(rule.sym2, p))
      if(reuse2Buffer(p*2+1) != VarIdx.none)
        m.aload(cells(reuse2)).iload(reuse2Buffer(p*2+1)).putfield(cell_aport(rule.sym2, p))
    }

    if(config.useCellCache && !isInitial) {
      if(reuse1 == -1) m.aload(cLeft).invokestatic(cellCache_set(rule.sym1))
      if(reuse2 == -1) m.aload(cRight).invokestatic(cellCache_set(rule.sym2))
    }

    if(config.collectStats) {
      m.aload(ptw).iload(statCellAllocations).iload(statCachedCellReuse).iconst(statSingletonUse)
      if(cont1 != VarIdx.none) {
        m.aload(cont1).ifNonNullThenElse(m.iconst(1))(m.iconst(0))
      } else m.iconst(0)
      m.invoke(ptw_recordStats)
    }

    if(cont1 != VarIdx.none) {
      m.aload(cont1).ifNonNullThen {
        m.aload(cont1).astore(cLeft).aload(cont2).astore(cRight)
        m.aconst_null.dup.astore(cont1).astore(cont2)
        m.goto(loopStart)
      }
    }

    if(methodEnd != null) m.goto(methodEnd)
    if(branch.condition.isDefined) m.setLabel(branchEnd)
  }

  private def findReuse(rule: GenericRulePlan, branch: BranchPlan): (Int, Int, Set[Connection]) = {
    if(!config.reuseCells) return (-1, -1, Set.empty)

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

  // Find unique continuation symbols for a rule plus a list of their eligible cell indices per branch
  private def uniqueContinuationsFor(rule: RulePlan, rules: scala.collection.Map[RuleKey, RulePlan]): (Set[Symbol], Vector[Vector[Int]]) = {
    if(config.inlineUniqueContinuations) {
      val funcSym =
        if(rule.derived) null
        else {
          val s = Set(rule.sym1, rule.sym2).filter(_.isDef)
          if(s.size == 1) s.head else null
        }
      if(funcSym != null) {
        val rhsSymsMap = rules.view.filterNot(_._2.derived).mapValues(_.branches.iterator.flatMap(_.cells).toSet)
        val rhsSymsHere = rhsSymsMap.iterator.filter { case (k, _) => k.sym1 == funcSym || k.sym2 == funcSym }.map(_._2).flatten.toSet
        val otherRhsSyms = rhsSymsMap.iterator.filter { case (k, _) => k.sym1 != funcSym && k.sym2 != funcSym }.map(_._2).flatten.toSet
        val unique = (rhsSymsHere -- otherRhsSyms).filter(s => s.isDef && s != funcSym && s.id != "dup" && s.id != "erase")
        val completions = rule.branches.map { branch =>
          (for {
            (s, i) <- branch.cells.zipWithIndex if unique.contains(s)
          } yield {
            branch.principalConns(i) match {
              case CellIdx(_, -1) => i //TODO not needed if rhs is fully reduced
              case FreeIdx(_, _) => i
              case _ => -1
          }}).filter(_ >= 0)
        }
        (unique, completions)
      } else (Set.empty, rule.branches.map(_ => Vector.empty))
    } else (Set.empty, rule.branches.map(_ => Vector.empty))
  }

  // maximize # of connections that can be made in the constructor calls
  private def optimizeCellCreationOrder(cellCount: Int, conns: Iterable[Connection]): ArrayBuffer[Int] = {
    val inc: Option[Int] => Option[Int] = { case Some(i) => Some(i+1); case None => Some(1) }
    lazy val cells = ArrayBuffer.tabulate(cellCount)(new C(_))
    class C(val idx: Int) {
      val in, out = mutable.HashMap.empty[C, Int]
      var weight: Int = 0
      def link(c: C): Unit = {
        out.updateWith(c)(inc)
        c.in.updateWith(this)(inc)
        weight += 1
      }
      def unlink(): Unit = {
        out.keys.foreach(c => c.in.remove(this))
        in.keys.foreach(c => c.out.remove(this).foreach { w => c.weight -= w })
      }
    }
    conns.foreach { case Connection(CellIdx(i1, p1), CellIdx(i2, p2)) =>
      if(p1 >= 0) cells(i1).link(cells(i2))
      if(p2 >= 0) cells(i2).link(cells(i1))
    }
    val order = ArrayBuffer.empty[Int]
    def take() = {
      val c = cells.head
      cells.remove(0)
      order += c.idx
      c.unlink()
    }
    while(cells.nonEmpty) { //TODO use heap
      cells.sortInPlaceBy(c => c.weight)
      if(cells.head.weight == 0)
        while(cells.nonEmpty && cells.head.weight == 0) take()
      else take()
    }
    order
  }

  private def incMetric(metric: String, m: MethodDSL, ptw: VarIdx): Unit =
    if(config.collectStats) m.aload(ptw).ldc(metric).iconst(1).invoke(ptw_recordMetric)

  private def compileInterface(sym: Symbol): Unit = {
    val ifm = interfaceMethod(sym)
    val c = new ClassDSL(Acc.PUBLIC | Acc.INTERFACE, ifm.owner.className)
    c.method(Acc.PUBLIC | Acc.ABSTRACT, ifm.name, ifm.desc)
    addClass(classLoader, c)
  }

  private def compileCell(sym: Symbol, rules: scala.collection.Map[RuleKey, _], common: scala.collection.Set[Symbol]): Class[_] = {
    val rulePairs = rules.keys.iterator.collect {
      case rk if rk.sym1 == sym => (rk.sym2, rk)
      case rk if rk.sym2 == sym => (rk.sym1, rk)
    }.toMap
    val interfaces = (rulePairs.keySet -- common).iterator.map(s => interfaceT(s).className).toArray.sorted
    val payloadInterfaces = sym.payloadType match {
      case PayloadType.INT => Vector(intBoxT.className)
      case PayloadType.REF | PayloadType.LABEL => Vector(refBoxT.className)
      case _ => Vector.empty
    }
    val c = new ClassDSL(Acc.PUBLIC | Acc.FINAL, concreteCellTFor(sym).className, commonCellT, interfaces ++ payloadInterfaces)

    val (cfields, pfields) = (0 until sym.arity).map(i => (c.field(Acc.PUBLIC, s"acell$i", cellT), c.field(Acc.PUBLIC, s"aport$i", tp.I))).unzip

    // accessors
    c.method(Acc.PUBLIC | Acc.FINAL, cell_arity).iconst(sym.arity).ireturn

    {
      val m = c.method(Acc.PUBLIC | Acc.FINAL, cell_auxCell)
      val p1 = m.param("p1", tp.I, Acc.FINAL)
      sym.arity match {
        case 0 => m.aconst_null.areturn
        case 1 => m.aload(m.receiver).getfield(cfields(0)).areturn
        case a => m.aload(m.receiver).iload(p1).tableSwitch(0, (0 until a).map { i => () => m.getfield(cfields(i)).areturn }: _*)
      }
    }

    {
      val m = c.method(Acc.PUBLIC | Acc.FINAL, cell_auxPort)
      val p1 = m.param("p1", tp.I, Acc.FINAL)
      sym.arity match {
        case 0 => m.iconst(0).ireturn
        case 1 => m.aload(m.receiver).getfield(pfields(0)).ireturn
        case a => m.aload(m.receiver).iload(p1).tableSwitch(0, (0 until a).map { i => () => m.getfield(pfields(i)).ireturn }: _*)
      }
    }

    {
      val m = c.method(Acc.PUBLIC | Acc.FINAL, cell_setAux)
      val p1 = m.param("p1", tp.I, Acc.FINAL)
      val c2 = m.param("c2", cellT, Acc.FINAL)
      val p2 = m.param("p2", tp.I, Acc.FINAL)
      sym.arity match {
        case 0 => m.return_
        case 1 => m.aload(m.receiver).dup.aload(c2).putfield(cfields(0)).iload(p2).putfield(pfields(0)).return_
        case a => m.aload(m.receiver).dup.iload(p1).tableSwitch(0, (0 until a).map { i => () => m.aload(c2).putfield(cfields(i)).iload(p2).putfield(pfields(i)).return_ }: _*)
      }
    }

    // constructor
    {
      val params = (0 until sym.arity).flatMap(_ => Seq(cellT, tp.I))
      val m = c.constructor(if(isSingleton(sym)) Acc.PRIVATE else Acc.PUBLIC, tp.m(params: _*))
      val aux = (0 until sym.arity).map(i => (m.param(s"c$i", cellT), m.param(s"p$i", tp.I)))
      m.aload(m.receiver).invokespecial(new_CommonCell)
      aux.zip(cfields).zip(pfields).foreach { case (((auxc, auxp), cfield), pfield) =>
        m.aload(m.receiver).dup.aload(auxc).putfield(cfield).iload(auxp).putfield(pfield)
      }
      m.return_
      if(isSingleton(sym)) {
        val fref = cell_singleton(sym)
        c.field(Acc.PUBLIC | Acc.STATIC | Acc.FINAL, fref)
        c.clinit().newInitDup(concreteConstrFor(sym))().putstatic(fref).return_
      }
    }

    // reinit
    if(sym.arity > 0) {
      val m = c.method(Acc.PUBLIC, concreteReinitFor(sym))
      val aux = (0 until sym.arity).map(i => (m.param(s"c$i", cellT), m.param(s"p$i", tp.I)))
      aux.zip(cfields).zip(pfields).foreach { case (((auxc, auxp), cfield), pfield) =>
        m.aload(m.receiver).dup.aload(auxc).putfield(cfield).iload(auxp).putfield(pfield)
      }
      m.return_
    }

    // payload implementation
    if(sym.payloadType.isDefined) {
      val field = concretePayloadFieldFor(sym)
      c.field(Acc.PUBLIC, field)
      c.setter(field)
      c.getter(field)
    }

    // generic reduce
    {
      val m = c.method(Acc.PUBLIC | Acc.FINAL, cell_reduce.name, cell_reduce.desc)
      val other = m.param("other", cellT, Acc.FINAL)
      val ptw = m.param("ptw", ptwT, Acc.FINAL)
      incMetric(s"${c.name}.${m.name}", m, ptw)
      val isShared = common.contains(sym)
      val ifm = if(isShared) interfaceMethod(sym).on(commonCellT) else interfaceMethod(sym)
      m.aload(other)
      m.tryCatchGoto(tp.c[ClassCastException]) {
        m.checkcast(ifm.owner)
      } {
        m.pop
        m.aload(ptw).aload(m.receiver).aload(other).invoke(ptw_irreducible)
        m.return_
      }
      m.aload(m.receiver).aload(ptw)
      m.invoke(ifm)
      m.return_
    }

    // interface methods
    rulePairs.foreach { case (sym2, rk) =>
      val ifm = interfaceMethod(sym2)
      val m = c.method(Acc.PUBLIC | Acc.FINAL, ifm.name, ifm.desc)
      val other = m.param("other", concreteCellTFor(sym2), Acc.FINAL)
      val ptw = m.param("ptw", ptwT, Acc.FINAL)
      incMetric(s"${c.name}.${m.name}", m, ptw)
      val staticMR = ruleT_static_reduce(rk.sym1, rk.sym2)
      if(rk.sym1 == sym) m.aload(m.receiver).aload(other)
      else m.aload(other).aload(m.receiver)
      m.aload(ptw).invokestatic(staticMR).return_
    }
    // unsupported common operations (when using config.allCommon)
    (common -- rulePairs.keySet).foreach { sym2 =>
      val ifm = interfaceMethod(sym2)
      val m = c.method(Acc.PUBLIC | Acc.FINAL, ifm.name, ifm.desc)
      val other = m.param("other", concreteCellTFor(sym2), Acc.FINAL)
      val ptw = m.param("ptw", ptwT, Acc.FINAL)
      m.aload(ptw).aload(m.receiver).aload(other).invoke(ptw_irreducible).return_
    }
    addClass(classLoader, c)
  }

  private def compileCommonCell(common: scala.collection.Set[Symbol]): Unit = {
    val c = new ClassDSL(Acc.PUBLIC | Acc.ABSTRACT, commonCellT.className, cellT)
    c.emptyNoArgsConstructor(Acc.PROTECTED)
    common.foreach(sym => c.method(Acc.PUBLIC | Acc.ABSTRACT, interfaceMethod(sym)))
    addClass(classLoader, c)
  }

  // find symbols that can interact with every symbol (usually dup & erase)
  private def findCommonPartners(rules: scala.collection.Map[RuleKey, RulePlan]): scala.collection.Set[Symbol] = {
    val ruleMap = mutable.HashMap.empty[Symbol, mutable.HashSet[Symbol]]
    rules.foreach { case (k, _) =>
      ruleMap.getOrElseUpdate(k.sym1, mutable.HashSet.empty) += k.sym2
      ruleMap.getOrElseUpdate(k.sym2, mutable.HashSet.empty) += k.sym1
    }
    if(config.allCommon) ruleMap.keySet
    else {
      val totalSyms = ruleMap.size
      val counts = mutable.HashMap.empty[Symbol, Int]
      for {
        v <- ruleMap.valuesIterator
        s <- v
      } {
        counts.updateWith(s) {
          case None => Some(1)
          case Some(x) => Some(x+1)
        }
      }
      counts.iterator.filter(_._2 == totalSyms).map(_._1).toSet
    }
  }

  private def compileCellCache(rules: scala.collection.Map[RuleKey, RulePlan]): Unit = {
    val syms = ((for {
      r <- rules.valuesIterator
      b <- r.branches.iterator
      s <- b.cells.iterator
    } yield s) ++ (rules.keysIterator.map(_.sym1) ++ rules.keysIterator.map(_.sym1)).filter(_.isDefined)).toVector.distinct.sortBy(_.id)
    val c = new ClassDSL(Acc.PUBLIC | Acc.FINAL, cellCacheT.className)
    c.emptyNoArgsConstructor(Acc.PRIVATE)
    syms.foreach { sym => c.field(Acc.PRIVATE | Acc.STATIC, cellCache_var(sym)) }
    syms.foreach { sym =>
      val m = c.method(Acc.PUBLIC | Acc.STATIC | Acc.FINAL, cellCache_get(sym))
      val f = cellCache_var(sym)
      m.getstatic(f).aconst_null.putstatic(f).areturn
    }
    syms.foreach { sym =>
      val m = c.method(Acc.PUBLIC | Acc.STATIC | Acc.FINAL, cellCache_set(sym))
      val cell = m.param("cell", concreteCellTFor(sym), Acc.FINAL)
      m.aload(cell).putstatic(cellCache_var(sym)).return_
    }
    addClass(classLoader, c)
  }

  private def compileInitial(rule: InitialPlan, initialIndex: Int): RuleImpl = {
    val staticMR = initialRuleT_static_reduce(initialIndex)
    val c = new ClassDSL(Acc.PUBLIC | Acc.FINAL, staticMR.owner.className, riT)
    c.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(c, rule, staticMR, Set.empty, Map.empty)

    // reduce
    {
      val m = c.method(Acc.PUBLIC | Acc.FINAL, ri_reduce)
      val c1 = m.param("c1", cellT, Acc.FINAL)
      val c2 = m.param("c2", cellT, Acc.FINAL)
      val ptw = m.param("ptw", ptwT, Acc.FINAL)
      m.aload(c1).aload(c2).aload(ptw).invokestatic(staticMR).return_
    }

    addClass(classLoader, c)
    classLoader.loadClass(c.javaName).getDeclaredConstructor().newInstance().asInstanceOf[RuleImpl]
  }

  private def compileRule(rule: RulePlan, shared: scala.collection.Set[Symbol], rules: scala.collection.Map[RuleKey, RulePlan]): Class[_] = {
    val staticMR = ruleT_static_reduce(rule.sym1, rule.sym2)
    val ric = new ClassDSL(Acc.PUBLIC | Acc.FINAL, staticMR.owner.className)
    ric.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(ric, rule, staticMR, shared, rules)
    addClass(classLoader, ric)
    classLoader.loadClass(ric.javaName)
  }

  def compile(rules: scala.collection.Map[RuleKey, RulePlan], initialRules: Iterable[InitialPlan], globals: Symbols): (Vector[(Vector[Symbol], RuleImpl)], Map[Class[_], Symbol]) = {
    val common = findCommonPartners(rules)
    val classToSymbol = Map.newBuilder[Class[_], Symbol]
    ParSupport.foreach(globals.symbols.filter(s => s.isCons && !common.contains(s)), config.compilerParallelism)(compileInterface)
    compileCommonCell(common)
    if(config.useCellCache) compileCellCache(rules)
    ParSupport.foreach(globals.symbols.filter(_.isCons), config.compilerParallelism) { sym =>
      val cls = compileCell(sym, rules, common)
      classToSymbol.synchronized(classToSymbol += ((cls, sym)))
    }
    ParSupport.foreach(rules.values, config.compilerParallelism) { g => compileRule(g, common, rules) }
    val initial = Vector.newBuilder[(Vector[Symbol], RuleImpl)]
    initialRules.zipWithIndex.foreach { case (ip, i) =>
      val ri = compileInitial(ip, i)
      initial += ((ip.free, ri))
    }
    (initial.result(), classToSymbol.result())
  }
}
