package de.szeiger.interact.st

import de.szeiger.interact.codegen.{AbstractCodeGen, LocalClassLoader, ParSupport}
import de.szeiger.interact.{Config, BranchPlan, BranchWiring, CellIdx, Connection, CreateLabelsComp, EmbArg, FreeIdx, GenericRuleWiring, GetSingletonCell, Global, Idx, InitialRuleWiring, IntBox, IntBoxImpl, NewCell, PayloadAssignment, PayloadComputation, PayloadMethodApplication, PayloadMethodApplicationWithReturn, PlanRules, RefBox, RefBoxImpl, Reuse1, Reuse2, RuleKey, RuleWiring, Runtime}
import de.szeiger.interact.ast.{EmbeddedType, PayloadType, Symbol, Symbols}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

import scala.collection.mutable

class CodeGen(genPackage: String, classLoader: LocalClassLoader, config: Config,
  rules: scala.collection.Map[RuleKey, RuleWiring], initialRules: Iterable[InitialRuleWiring], globals: Symbols) extends AbstractCodeGen[RuleImpl](config) {

  val common = findCommonPartners()
  val planner = new PlanRules(config)

  private val riT = tp.c[RuleImpl]
  private val ptwT = tp.c[PerThreadWorker]
  private val cellT = tp.c[Cell]
  private val intBoxT = tp.i[IntBox]
  private val refBoxT = tp.i[RefBox]
  private val intBoxImplT = tp.c[IntBoxImpl]
  private val refBoxImplT = tp.c[RefBoxImpl]
  private val commonCellT = tp.c(s"$genPackage/CommonCell")
  private val cellCacheT = tp.c(s"$genPackage/CellCache")
  private val ri_reduce = riT.method("reduce", tp.m(cellT, cellT, ptwT).V)
  private val cell_reduce = cellT.method("reduce", tp.m(cellT, ptwT).V)
  private val cell_arity = cellT.method("arity", tp.m().I)
  private val cell_auxCell = cellT.method("auxCell", tp.m(tp.I)(cellT))
  private val cell_auxPort = cellT.method("auxPort", tp.m(tp.I).I)
  private val cell_setAux = cellT.method("setAux", tp.m(tp.I, cellT, tp.I).V)
  private val ptw_createCut = ptwT.method("createCut", tp.m(cellT, cellT).V)
  private val ptw_recordStats = ptwT.method("recordStats", tp.m(tp.I, tp.I, tp.I, tp.I, tp.I).V)
  private val ptw_recordMetric = ptwT.method("recordMetric", tp.m(tp.c[String], tp.I).V)
  private val ptw_irreducible = ptwT.method("irreducible", tp.m(cellT, cellT).V)
  private val intBox_getValue = intBoxT.method("getValue", tp.m().I)
  private val intBox_setValue = intBoxT.method("setValue", tp.m(tp.I).V)
  private val refBox_getValue = refBoxT.method("getValue", tp.m()(tp.c[AnyRef]))
  private val refBox_setValue = refBoxT.method("setValue", tp.m(tp.c[AnyRef]).V)
  private val new_CommonCell = commonCellT.constr(tp.m().V)
  private val new_IntBoxImpl = intBoxImplT.constr(tp.m().V)
  private val new_RefBoxImpl = refBoxImplT.constr(tp.m().V)

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
  private def cellCache_var(sym: Symbol) = cellCacheT.field(s"f_${encodeName(sym)}", concreteCellTFor(sym))
  private def cellCache_get(sym: Symbol) = cellCacheT.method(s"get_${encodeName(sym)}", tp.m()(concreteCellTFor(sym)))
  private def cellCache_set(sym: Symbol) = cellCacheT.method(s"set_${encodeName(sym)}", tp.m(concreteCellTFor(sym)).V)

  private def implementStaticReduce(c: ClassDSL, rule: GenericRuleWiring, mref: MethodRef): Unit = {
    val m = c.method(Acc.PUBLIC.STATIC, mref.name, mref.desc)
    val cLeftTp = concreteCellTFor(rule.sym1)
    val cRightTp = concreteCellTFor(rule.sym2)
    val cLeft = m.param("cLeft", cLeftTp)
    val cRight = m.param("cRight", cRightTp)
    val ptw = m.param("ptw", ptwT)
    incMetric(s"${c.name}.${m.name}", m, ptw)
    val methodEnd = if(rule.branches.length > 1) m.newLabel else null
    val methodStart = m.setLabel()
    rule.branches.foreach { branch =>
      emitBranchReduce(m: MethodDSL, rule, branch, rule.isInstanceOf[InitialRuleWiring], cLeft, cRight, cLeftTp, cRightTp, ptw, methodStart, methodEnd)
    }
    if(methodEnd != null) m.setLabel(methodEnd)
    m.return_
  }

  private def emitBranchReduce(m: MethodDSL, rule: GenericRuleWiring, branch: BranchWiring, isInitial: Boolean,
      cLeft: VarIdx, cRight: VarIdx, cLeftTp: ClassOwner, cRightTp: ClassOwner, ptw: VarIdx, methodStart: Label, methodEnd: Label): Unit = {
    val be = planner(rule, branch, rules)
    val branchEnd = m.newLabel

    be.cond.foreach { case pc: PayloadMethodApplication =>
      def adaptPayloadFromCell(cell: VarIdx, cellTp: Owner, cls: Class[_]): Unit = {
        m.aload(cell)
        if(cls == classOf[Int]) m.invoke(intBox_getValue, cellTp)
        else if(cls == classOf[AnyRef]) m.invoke(refBox_getValue, cellTp)
        else m.invoke(refBox_getValue, cellTp).checkcast(tp.o(cls))
      }
      assert(pc.jMethod.getReturnType == classOf[Boolean])
      callPayloadMethod(m, pc, branchEnd) {
        pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach {
          case (EmbArg.Const(i: Int), _) => m.iconst(i)
          case (EmbArg.Const(s: String), _) => m.ldc(s)
          case (EmbArg.Left, cls) => adaptPayloadFromCell(cLeft, cLeftTp, cls)
          case (EmbArg.Right, cls) => adaptPayloadFromCell(cRight, cRightTp, cls)
        }
      }
    }

    val (cont1, cont2) = {
      if(be.loopOn1 || be.loopOn2) {
        val cont1 = m.aconst_null.storeLocal(concreteCellTFor(rule.sym1))
        val cont2 = m.aconst_null.storeLocal(concreteCellTFor(rule.sym2))
        (cont1, cont2)
      } else (VarIdx.none, VarIdx.none)
    }

    val statCellAllocations, statCachedCellReuse = if(config.collectStats) m.iconst(0).storeLocal(tp.I) else VarIdx.none
    val cells = Array.fill[VarIdx](be.cellCount)(VarIdx.none)
    val reuse1Buffer = Array.fill[VarIdx](rule.arity1*2)(VarIdx.none)
    val reuse2Buffer = Array.fill[VarIdx](rule.arity2*2)(VarIdx.none)

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

    // Write to reuse buffer
    def setReuse(buf: Array[VarIdx], port: Int, ct2: Idx): Unit = {
      ldBoth(ct2)
      buf(port*2+1) = m.storeLocal(tp.I)
      buf(port*2) = m.storeLocal(cellT)
    }

    // Write to internal cell or reuse buffer for reused cells
    def setAux(idx: CellIdx, ct2: Idx, setPort: Boolean = true): Unit = {
      val sym = branch.cells(idx.idx)
      if(idx.idx == be.reuse1) setReuse(reuse1Buffer, idx.port, ct2)
      else if(idx.idx == be.reuse2) setReuse(reuse2Buffer, idx.port, ct2)
      else {
        m.aload(cells(idx.idx))
        if(setPort) m.dup
        ldCell(ct2).putfield(cell_acell(sym, idx.port))
        if(setPort) ldPort(ct2).putfield(cell_aport(sym, idx.port))
      }
    }

    // Create new cells
    be.cellCreateInstructions.foreach {
      case GetSingletonCell(idx, sym) =>
        val constr = concreteConstrFor(sym)
        cells(idx) = m.getstatic(cell_singleton(sym)).storeLocal(constr.tpe, s"c$idx")
      case Reuse1(idx) => cells(idx) = cLeft
      case Reuse2(idx) => cells(idx) = cRight
      case NewCell(idx, sym, args) =>
        val constr = concreteConstrFor(sym)
        def loadParams(): Unit = args.foreach {
          case CellIdx(-1, p) => m.aconst_null.iconst(p)
          case CellIdx(c, p) => m.aload(cells(c)).iconst(p)
          case f: FreeIdx => ldBoth(f)
        }
        if(isInitial || !config.useCellCache) {
          m.newInitDup(constr)(loadParams())
          if(config.collectStats) m.iinc(statCellAllocations)
        } else {
          m.invokestatic(cellCache_get(sym)).dup.ifNull.thnElse {
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
        cells(idx) = m.storeLocal(constr.tpe, s"c$idx")
    }

    computePayloads(m, be, cells, cLeft, cRight, rule.sym1.payloadType, rule.sym2.payloadType)

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
      if(be.isReuse(ct1) && ct1.isAux)
        setAux(ct1, ct2)
      if(ct1.isPrincipal) {
        ldPort(ct2).if_>=.thnElse {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        } {
          if(ct1.idx == be.reuse1 && be.loopOn1) {
            m.aload(cont1).ifNull.and {
              ldCell(ct2).instanceof(concreteCellTFor(rule.sym2))
            }.if_!=.thnElse {
              ldCell(ct1).astore(cont1)
              ldCell(ct2).checkcast(concreteCellTFor(rule.sym2)).astore(cont2)
            } {
              createCut(ct1, ct2)
            }
          } else if(ct1.idx == be.reuse2 && be.loopOn2) {
            m.aload(cont1).ifNull.and {
              ldCell(ct2).instanceof(concreteCellTFor(rule.sym1))
            }.if_!=.thnElse {
              ldCell(ct1).astore(cont2)
              ldCell(ct2).checkcast(concreteCellTFor(rule.sym1)).astore(cont1)
            } {
              createCut(ct1, ct2)
            }
          } else createCut(ct1, ct2)
        }
      } else {
        ldPort(ct2).if_>=.thn {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        }
      }
    }
    def connectFF(ct1: FreeIdx, ct2: FreeIdx): Unit = {
      ldPort(ct1).if_>=.thnElse {
        ldBoth(ct1); ldBoth(ct2).invoke(cell_setAux)
        ldPort(ct2).if_>=.thn {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        }
      } {
        ldPort(ct2).if_>=.thnElse {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        } {
          createCut(ct1, ct2)
        }
      }
    }
    def connectCC(ct1: CellIdx, ct2: CellIdx): Unit = {
      if(ct1.isAux && !be.cellPortsConnected.contains(ct1))
        setAux(ct1, ct2, be.isReuse(ct1))
      if(ct2.isAux && !be.cellPortsConnected.contains(ct2))
        setAux(ct2, ct1, be.isReuse(ct2))
      if(ct1.isPrincipal && ct2.isPrincipal)
        createCut(ct1, ct2)
    }
    be.sortedConns.foreach {
      case Connection(i1: FreeIdx, i2: FreeIdx) => connectFF(i1, i2)
      case Connection(i1: FreeIdx, i2: CellIdx) => connectCF(i2, i1)
      case Connection(i1: CellIdx, i2: FreeIdx) => connectCF(i1, i2)
      case Connection(i1: CellIdx, i2: CellIdx) => connectCC(i1, i2)
    }

    if(be.reuse1 != -1) flushReuseBuffer(m, reuse1Buffer, cells(be.reuse1), rule.sym1)
    if(be.reuse2 != -1) flushReuseBuffer(m, reuse2Buffer, cells(be.reuse2), rule.sym2)

    if(config.useCellCache && !isInitial) {
      if(be.reuse1 == -1) m.aload(cLeft).invokestatic(cellCache_set(rule.sym1))
      if(be.reuse2 == -1) m.aload(cRight).invokestatic(cellCache_set(rule.sym2))
    }

    if(config.collectStats) {
      m.aload(ptw).iload(statCellAllocations).iload(statCachedCellReuse).iconst(be.statSingletonUse)
      if(cont1 != VarIdx.none) m.aload(cont1).ifNonNull.thnElse(m.iconst(1))(m.iconst(0))
      else m.iconst(0)
      m.iconst(be.statLabelCreate).invoke(ptw_recordStats)
    }

    if(cont1 != VarIdx.none) {
      m.aload(cont1).ifNonNull.thn {
        m.aload(cont1).astore(cLeft).aload(cont2).astore(cRight)
        m.aconst_null.dup.astore(cont1).astore(cont2)
        m.goto(methodStart) //TODO jump directly to the right branch if it can be determined statically
      }
    }

    if(methodEnd != null) m.goto(methodEnd)
    if(branch.cond.isDefined) m.setLabel(branchEnd)
  }

  private def flushReuseBuffer(m: MethodDSL, b: Array[VarIdx], cell: VarIdx, cellSym: Symbol): Unit =
    for(p <- 0 until b.length/2) {
      if(b(p*2) != VarIdx.none)
        m.aload(cell).aload(b(p*2)).putfield(cell_acell(cellSym, p))
      if(b(p*2+1) != VarIdx.none)
        m.aload(cell).iload(b(p*2+1)).putfield(cell_aport(cellSym, p))
    }

  private def computePayloads(m: MethodDSL, be: BranchPlan, cells: scala.collection.Seq[VarIdx], cLeft: VarIdx, cRight: VarIdx, pt1: PayloadType, pt2: PayloadType): Unit = {
    val temp = be.payloadTemp.map {
      //TODO use cached boxes
      case (PayloadType.INT, true) => m.newInitDup(new_IntBoxImpl)().storeLocal(intBoxImplT)
      case (PayloadType.INT, false) => m.local(tp.I)
      case (_, true) => m.newInitDup(new_RefBoxImpl)().storeLocal(refBoxImplT)
      case (_, false) => m.local(tp.c[AnyRef])
    }
    def unboxedTemp(ea: EmbArg): Option[VarIdx] = ea match {
      case EmbArg.Temp(idx, _) if !be.payloadTemp(idx)._2 => Some(temp(idx))
      case _ => None
    }
    def cache(cell: VarIdx, pt: PayloadType): VarIdx = pt match {
      case PayloadType.VOID => VarIdx.none
      case PayloadType.INT => m.aload(cell).invoke(intBox_getValue).storeLocal(tp.I)
      case _ => m.aload(cell).invoke(refBox_getValue).storeLocal(tp.c[AnyRef])
    }
    val cachedPayload1 = cache(cLeft, pt1)
    val cachedPayload2 = cache(cRight, pt2)
    def loadArg(embArg: EmbArg, cls: Class[_]): Unit = embArg match {
      case EmbArg.Const(i: Int) => m.iconst(i)
      case EmbArg.Const(s: String) => m.ldc(s)
      case EmbArg.Left => adaptCachedPayload(cachedPayload1, cls)
      case EmbArg.Right => adaptCachedPayload(cachedPayload2, cls)
      case EmbArg.Cell(idx) => m.aload(cells(idx))
      case EmbArg.Temp(idx, _) => adaptTempPayload(idx, cls)
    }
    be.createLabelComps.foreach { case (pc, idx) =>
      if(idx == -1) m.newInitDup(tp.c[AnyRef].constr(tp.m().V))()
      else m.aload(cells(idx))
      pc.embArgs.indices.foreach { i =>
        if(i != pc.embArgs.length-1) m.dup
        unboxedTemp(pc.embArgs(i)) match {
          case Some(vi) =>
            m.astore(vi)
          case None =>
            loadArg(pc.embArgs(i), classOf[RefBox])
            m.swap.invoke(refBox_setValue)
        }
      }
    }
    def adaptCachedPayload(cached: VarIdx, cls: Class[_]): Unit = {
      if(cls == classOf[Int]) m.iload(cached)
      else {
        m.aload(cached)
        if(cls != classOf[AnyRef]) m.checkcast(tp.o(cls))
      }
    }
    def adaptTempPayload(idx: Int, cls: Class[_]): Unit = {
      if(cls == classOf[Int]) {
        if(be.payloadTemp(idx)._2) m.aload(temp(idx)).invoke(intBox_getValue)
        else m.iload(temp(idx))
      } else if(cls == classOf[IntBox] || cls == classOf[RefBox]) m.aload(temp(idx))
      else {
        if(be.payloadTemp(idx)._2) m.aload(temp(idx)).invoke(refBox_getValue)
        else m.aload(temp(idx))
        if(cls != classOf[AnyRef]) m.checkcast(tp.o(cls))
      }
    }
    def setCellValue(embArg: EmbArg.Cell, cls: Class[_]): Unit =
      m.aload(cells(embArg.idx)).swap.invoke(if(cls == classOf[Int]) intBox_setValue else refBox_setValue)
    def loadArgs(pc: PayloadMethodApplication): Unit =
      pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach { case (embArg, cls) => loadArg(embArg, cls) }
    be.otherPayloadComps.foreach {
      case pc: PayloadMethodApplication =>
        assert(pc.jMethod.getReturnType == Void.TYPE)
        callPayloadMethod(m, pc)(loadArgs(pc))
      case pc: PayloadAssignment =>
        assert(pc.payloadType.isDefined)
        if(pc.payloadType == PayloadType.INT) {
          unboxedTemp(pc.targetIdx) match {
            case Some(vi) =>
              loadArg(pc.sourceIdx, classOf[Int])
              m.istore(vi)
            case None =>
              loadArg(pc.targetIdx, classOf[IntBox])
              loadArg(pc.sourceIdx, classOf[Int])
              m.invoke(intBox_setValue)
          }
        } else {
          unboxedTemp(pc.targetIdx) match {
            case Some(vi) =>
              loadArg(pc.sourceIdx, classOf[AnyRef])
              m.astore(vi)
            case None =>
              loadArg(pc.targetIdx, classOf[RefBox])
              loadArg(pc.sourceIdx, classOf[AnyRef])
              m.invoke(refBox_setValue)
          }
        }
      case pc: PayloadMethodApplicationWithReturn =>
        callPayloadMethod(m, pc.method)(loadArgs(pc.method))
        unboxedTemp(pc.retIndex) match {
          case Some(vi) =>
            if(pc.method.embTp.ret == EmbeddedType.PayloadInt) m.istore(vi)
            else m.astore(vi)
          case None =>
            setCellValue(pc.retIndex.asInstanceOf[EmbArg.Cell], pc.method.jMethod.getReturnType)
        }
    }
  }

  private def callPayloadMethod(m: MethodDSL, pc: PayloadMethodApplication, elseTarget: Label = null)(loadArgs: => Unit): Unit = {
    val RuntimeCls = classOf[Runtime.type].getName
    (pc.jMethod.getDeclaringClass.getName, pc.jMethod.getName, pc.embTp.args) match {
      case (RuntimeCls, "eq", Vector((EmbeddedType.PayloadInt, false), (EmbeddedType.PayloadInt, false))) if elseTarget != null =>
        loadArgs
        m.ifI_!=.jump(elseTarget)
      case (RuntimeCls, "eqLabel", Vector((EmbeddedType.PayloadLabel, false), (EmbeddedType.PayloadLabel, false))) if elseTarget != null =>
        loadArgs
        m.ifA_!=.jump(elseTarget)
      case _ =>
        val mref = MethodRef(pc.jMethod)
        if(pc.isStatic) {
          loadArgs
          m.invokestatic(mref)
        } else {
          m.getstatic(mref.owner.field("MODULE$", mref.owner))
          loadArgs
          m.invoke(mref)
        }
        if(elseTarget != null) m.ifeq(elseTarget)
    }
  }

  private def incMetric(metric: String, m: MethodDSL, ptw: VarIdx): Unit =
    if(config.collectStats) m.aload(ptw).ldc(metric).iconst(1).invoke(ptw_recordMetric)

  private def compileInterface(sym: Symbol): Unit = {
    val ifm = interfaceMethod(sym)
    val c = DSL.newInterface(Acc.PUBLIC, ifm.owner.className)
    c.method(Acc.PUBLIC.ABSTRACT, ifm.name, ifm.desc)
    addClass(classLoader, c)
  }

  private def compileCell(sym: Symbol): Class[_] = {
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
    val c = DSL.newClass(Acc.PUBLIC.FINAL, concreteCellTFor(sym).className, commonCellT, interfaces ++ payloadInterfaces)

    val (cfields, pfields) = (0 until sym.arity).map(i => (c.field(Acc.PUBLIC, s"acell$i", cellT), c.field(Acc.PUBLIC, s"aport$i", tp.I))).unzip

    // accessors
    c.method(Acc.PUBLIC.FINAL, cell_arity).iconst(sym.arity).ireturn

    {
      val m = c.method(Acc.PUBLIC.FINAL, cell_auxCell)
      val p1 = m.param("p1", tp.I)
      sym.arity match {
        case 0 => m.aconst_null.areturn
        case 1 => m.aload(m.receiver).getfield(cfields(0)).areturn
        case a => m.aload(m.receiver).iload(p1).tableSwitch(0 until a-1) { io => m.getfield(cfields(io.getOrElse(a-1))).areturn }
      }
    }

    {
      val m = c.method(Acc.PUBLIC.FINAL, cell_auxPort)
      val p1 = m.param("p1", tp.I)
      sym.arity match {
        case 0 => m.iconst(0).ireturn
        case 1 => m.aload(m.receiver).getfield(pfields(0)).ireturn
        case a => m.aload(m.receiver).iload(p1).tableSwitch(0 until a-1) { io => m.getfield(pfields(io.getOrElse(a-1))).ireturn }
      }
    }

    {
      val m = c.method(Acc.PUBLIC.FINAL, cell_setAux)
      val p1 = m.param("p1", tp.I)
      val c2 = m.param("c2", cellT)
      val p2 = m.param("p2", tp.I)
      sym.arity match {
        case 0 => m.return_
        case 1 => m.aload(m.receiver).dup.aload(c2).putfield(cfields(0)).iload(p2).putfield(pfields(0)).return_
        case a => m.aload(m.receiver).dup.iload(p1).tableSwitch(0 until a-1) { io =>
          val i = io.getOrElse(a-1)
          m.aload(c2).putfield(cfields(i)).iload(p2).putfield(pfields(i)).return_
        }
      }
    }

    // constructor
    {
      val params = (0 until sym.arity).flatMap(_ => Seq(cellT, tp.I))
      val m = c.constructor(if(PlanRules.isSingleton(sym)) Acc.PRIVATE else Acc.PUBLIC, tp.m(params: _*))
      val aux = (0 until sym.arity).map(i => (m.param(s"c$i", cellT), m.param(s"p$i", tp.I)))
      m.aload(m.receiver).invokespecial(new_CommonCell)
      aux.zip(cfields).zip(pfields).foreach { case (((auxc, auxp), cfield), pfield) =>
        m.aload(m.receiver).dup.aload(auxc).putfield(cfield).iload(auxp).putfield(pfield)
      }
      m.return_
      if(PlanRules.isSingleton(sym)) {
        val fref = cell_singleton(sym)
        c.field(Acc.PUBLIC.STATIC.FINAL, fref)
        c.clinit().newInitDup(concreteConstrFor(sym))().putstatic(fref).return_
      }
    }

    // reinit
    if(sym.arity > 0 || sym.payloadType.isDefined) {
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
      val m = c.method(Acc.PUBLIC.FINAL, cell_reduce.name, cell_reduce.desc)
      val other = m.param("other", cellT)
      val ptw = m.param("ptw", ptwT)
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
      val m = c.method(Acc.PUBLIC.FINAL, ifm.name, ifm.desc)
      val other = m.param("other", concreteCellTFor(sym2))
      val ptw = m.param("ptw", ptwT)
      incMetric(s"${c.name}.${m.name}", m, ptw)
      val staticMR = ruleT_static_reduce(rk.sym1, rk.sym2)
      if(rk.sym1 == sym) m.aload(m.receiver).aload(other)
      else m.aload(other).aload(m.receiver)
      m.aload(ptw).invokestatic(staticMR).return_
    }
    // unsupported common operations (when using config.allCommon)
    (common -- rulePairs.keySet).foreach { sym2 =>
      val ifm = interfaceMethod(sym2)
      val m = c.method(Acc.PUBLIC.FINAL, ifm.name, ifm.desc)
      val other = m.param("other", concreteCellTFor(sym2))
      val ptw = m.param("ptw", ptwT)
      m.aload(ptw).aload(m.receiver).aload(other).invoke(ptw_irreducible).return_
    }
    addClass(classLoader, c)
  }

  private def compileCommonCell(): Unit = {
    val c = DSL.newClass(Acc.PUBLIC.ABSTRACT, commonCellT.className, cellT)
    c.emptyNoArgsConstructor(Acc.PROTECTED)
    common.foreach(sym => c.method(Acc.PUBLIC.ABSTRACT, interfaceMethod(sym)))
    addClass(classLoader, c)
  }

  // find symbols that can interact with every symbol (usually dup & erase)
  private def findCommonPartners(): scala.collection.Set[Symbol] = {
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

  private def compileCellCache(): Unit = {
    val syms = ((for {
      r <- rules.valuesIterator
      b <- r.branches.iterator
      s <- b.cells.iterator
    } yield s) ++ (rules.keysIterator.map(_.sym1) ++ rules.keysIterator.map(_.sym1)).filter(_.isDefined)).toVector.distinct.sortBy(_.id)
    val c = DSL.newClass(Acc.PUBLIC.FINAL, cellCacheT.className)
    c.emptyNoArgsConstructor(Acc.PRIVATE)
    syms.foreach { sym => c.field(Acc.PRIVATE.STATIC, cellCache_var(sym)) }
    syms.foreach { sym =>
      val m = c.method(Acc.PUBLIC.STATIC.FINAL, cellCache_get(sym))
      val f = cellCache_var(sym)
      m.getstatic(f).aconst_null.putstatic(f).areturn
    }
    syms.foreach { sym =>
      val m = c.method(Acc.PUBLIC.STATIC.FINAL, cellCache_set(sym))
      val cell = m.param("cell", concreteCellTFor(sym))
      m.aload(cell).putstatic(cellCache_var(sym)).return_
    }
    addClass(classLoader, c)
  }

  private def compileInitial(rule: InitialRuleWiring, initialIndex: Int): RuleImpl = {
    val staticMR = initialRuleT_static_reduce(initialIndex)
    val c = DSL.newClass(Acc.PUBLIC.FINAL, staticMR.owner.className, riT)
    c.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(c, rule, staticMR)

    // reduce
    {
      val m = c.method(Acc.PUBLIC.FINAL, ri_reduce)
      val c1 = m.param("c1", cellT)
      val c2 = m.param("c2", cellT)
      val ptw = m.param("ptw", ptwT)
      m.aload(c1).aload(c2).aload(ptw).invokestatic(staticMR).return_
    }

    addClass(classLoader, c)
    classLoader.loadClass(c.javaName).getDeclaredConstructor().newInstance().asInstanceOf[RuleImpl]
  }

  private def compileRule(rule: RuleWiring): Class[_] = {
    val staticMR = ruleT_static_reduce(rule.sym1, rule.sym2)
    val ric = DSL.newClass(Acc.PUBLIC.FINAL, staticMR.owner.className)
    ric.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(ric, rule, staticMR)
    addClass(classLoader, ric)
    classLoader.loadClass(ric.javaName)
  }

  def compile(): (Vector[(Vector[Symbol], RuleImpl)], Map[Class[_], Symbol]) = {
    val classToSymbol = Map.newBuilder[Class[_], Symbol]
    ParSupport.foreach(globals.symbols.filter(s => s.isCons && !common.contains(s)), config.compilerParallelism)(compileInterface)
    compileCommonCell()
    if(config.useCellCache) compileCellCache()
    ParSupport.foreach(globals.symbols.filter(_.isCons), config.compilerParallelism) { sym =>
      val cls = compileCell(sym)
      classToSymbol.synchronized(classToSymbol += ((cls, sym)))
    }
    ParSupport.foreach(rules.values, config.compilerParallelism)(compileRule)
    val initial = Vector.newBuilder[(Vector[Symbol], RuleImpl)]
    initialRules.zipWithIndex.foreach { case (ip, i) =>
      val ri = compileInitial(ip, i)
      initial += ((ip.free, ri))
    }
    (initial.result(), classToSymbol.result())
  }
}
