package de.szeiger.interact.st

import de.szeiger.interact.{AllocateTemp, BranchPlan, CellIdx, Config, Connection, CreateInstruction, CreateLabelsComp, EmbArg, FreeIdx, GetSingletonCell, Idx, IntBox, NewCell, PayloadAssignment, PayloadComputationPlan, PayloadMethodApplication, PayloadMethodApplicationWithReturn, RefBox, ReuseActiveCell, ReuseLabelsComp, RulePlan, Runtime}
import de.szeiger.interact.ast.{EmbeddedType, PayloadType, Symbol}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

class GenStaticReduce(m: MethodDSL, _initialActive: Vector[ActiveCell], ptw: VarIdx, rule: RulePlan, defs: Defs, config: Config, common: Set[Symbol]) {
  import defs._

  val methodEnd = if(rule.branches.length > 1 || rule.branches.head.branches.length > 0) m.newLabel else null
  val methodStart = m.setLabel()
  val statCellAllocations, statCachedCellReuse = if(config.collectStats) m.iconst(0).storeLocal(tp.I) else VarIdx.none
  // active cells (at least two, from the top-level rule)
  var active: Vector[ActiveCell] = _initialActive
  // cells and their symbols, updated for the current branches
  val cells = new VarIdxArray(rule.totalCellCount)
  val cellSyms = new Array[Symbol](rule.totalCellCount)
  // cell reuse buffers, updated for the current top-level branch
  var reuseBuffers: Vector[WriteBuffer] = Vector.empty
  // payload temp vars and boxed flag, updated for the current branches
  val temp = new Array[(VarIdx, Boolean)](rule.totalTempCount)
  // cached payloads, shared between all branches
  val cachedPayloads = active.map { ac =>
    ac.sym.payloadType match {
      case PayloadType.VOID => VarIdx.none
      case PayloadType.INT => m.aload(ac.idx).invoke(intBox_getValue).storeLocal(tp.I)
      case _ => m.aload(ac.idx).invoke(refBox_getValue).storeLocal(tp.c[AnyRef])
    }
  }

  // Local vars to buffer writes to a reused cell
  class WriteBuffer(ac: ActiveCell) {
    val cellIdx: Int = ac.reuse
    private[this] val cs, ps = new VarIdxArray(ac.arity)
    def set(port: Int, ct2: Idx): Unit = {
      ldBoth(ct2)
      ps(port) = m.storeLocal(tp.I)
      cs(port) = m.storeLocal(cellT)
    }
    def flush(): Unit =
      for(p <- 0 until cs.length) {
        if(cs(p) != VarIdx.none) m.aload(cells(cellIdx)).aload(cs(p)).putfield(cell_acell(ac.sym, p))
        if(ps(p) != VarIdx.none) m.aload(cells(cellIdx)).iload(ps(p)).putfield(cell_aport(ac.sym, p))
      }
  }

  // Cell accessors
  private def ldCell(idx: Idx) = idx match {
    case FreeIdx(ac, p) =>
      m.aload(active(ac).idx)
      if(rule.initial) m.iconst(p).invoke(cell_auxCell) else m.getfield(cell_acell(active(ac).sym, p))
    case CellIdx(i, _) => m.aload(cells(i))
  }
  private def ldPort(idx: Idx) = idx match {
    case FreeIdx(ac, p) =>
      m.aload(active(ac).idx)
      if(rule.initial) m.iconst(p).invoke(cell_auxPort) else m.getfield(cell_aport(active(ac).sym, p))
    case CellIdx(_, p) => m.iconst(p)
  }
  private def ldBoth(idx: Idx) = { ldCell(idx); ldPort(idx) }

  // Write to internal cell or reuse buffer for reused cells
  private def setAux(idx: CellIdx, ct2: Idx, setPort: Boolean = true): Unit =
    reuseBuffers.find(_.cellIdx == idx.idx) match {
      case Some(b) => b.set(idx.port, ct2)
      case None =>
        val sym = cellSyms(idx.idx)
        m.aload(cells(idx.idx))
        if(setPort) m.dup
        ldCell(ct2).putfield(cell_acell(sym, idx.port))
        if(setPort) ldPort(ct2).putfield(cell_aport(sym, idx.port))
    }

  private def createCut(ct1: Idx, ct2: Idx) = {
    m.aload(ptw);
    (ct1, ct2) match {
      case (_, CellIdx(idx, _)) if common.contains(cellSyms(idx)) => ldCell(ct2); ldCell(ct1)
      case (CellIdx(idx, _), _: FreeIdx) if !common.contains(cellSyms(idx)) => ldCell(ct2); ldCell(ct1)
      case _ => ldCell(ct1); ldCell(ct2)
    }
    m.invoke(ptw_createCut)
  }

  def emitBranch(bp: BranchPlan): Unit = {
    //println("***** entering "+bp.show)
    //ShowableNode.print(bp)
    cells.clearFrom(bp.cellOffset)
    bp.cellSyms.copyToArray(cellSyms, bp.cellOffset)
    val branchEnd = m.newLabel

    checkCond(bp.cond, branchEnd)

    val (cont1, cont2) = {
      if(bp.loopOn1 || bp.loopOn2) {
        val cont1 = m.aconst_null.storeLocal(concreteCellTFor(active(0).sym))
        val cont2 = m.aconst_null.storeLocal(concreteCellTFor(active(1).sym))
        (cont1, cont2)
      } else (VarIdx.none, VarIdx.none)
    }
    def setCont1(ct1: CellIdx, ct2: FreeIdx): Unit = {
      ldCell(ct1).astore(cont1)
      ldCell(ct2).checkcast(concreteCellTFor(active(1).sym)).astore(cont2)
    }
    def setCont2(ct1: CellIdx, ct2: FreeIdx): Unit = {
      ldCell(ct1).astore(cont2)
      ldCell(ct2).checkcast(concreteCellTFor(active(0).sym)).astore(cont1)
    }

    createCells(bp.cellCreateInstructions)

    computePayloads(bp)

    // Connect remaining wires
    def connectCF(ct1: CellIdx, ct2: FreeIdx): Unit = {
      if(ct1.isPrincipal) {
        ldPort(ct2).if_>=.thnElse {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        } {
          if(ct1.idx == bp.reuse1 && bp.loopOn1) {
            m.aload(cont1).ifNull.and {
              ldCell(ct2).instanceof(concreteCellTFor(active(1).sym))
            }.if_!=.thnElse { setCont1(ct1, ct2) } { createCut(ct1, ct2) }
          } else if(ct1.idx == bp.reuse2 && bp.loopOn2) {
            m.aload(cont1).ifNull.and {
              ldCell(ct2).instanceof(concreteCellTFor(active(0).sym))
            }.if_!=.thnElse { setCont2(ct1, ct2) } { createCut(ct1, ct2) }
          } else createCut(ct1, ct2)
        }
      } else {
        if(bp.isReuse(ct1)) setAux(ct1, ct2)
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
      if(ct1.isAux && !bp.cellPortsConnected.contains(ct1))
        setAux(ct1, ct2, bp.isReuse(ct1))
      if(ct2.isAux && !bp.cellPortsConnected.contains(ct2))
        setAux(ct2, ct1, bp.isReuse(ct2))
      if(ct1.isPrincipal && ct2.isPrincipal)
        createCut(ct1, ct2)
    }
    bp.sortedConns.foreach {
      case Connection(i1: FreeIdx, i2: FreeIdx) => connectFF(i1, i2)
      case Connection(i1: FreeIdx, i2: CellIdx) => connectCF(i2, i1)
      case Connection(i1: CellIdx, i2: FreeIdx) => connectCF(i1, i2)
      case Connection(i1: CellIdx, i2: CellIdx) => connectCC(i1, i2)
    }

    if(bp.branches.nonEmpty) bp.branches.foreach(b => emitBranch(b))
    else {
      reuseBuffers.foreach(_.flush())

      if(config.useCellCache && !rule.initial)
        active.foreach { case a if a.reuse == -1 => m.aload(a.idx).invokestatic(cellCache_set(a.sym)) }

      recordStats(cont1, bp)

      if(cont1 != VarIdx.none) {
        m.aload(cont1).ifNonNull.thn {
          m.aload(cont1).astore(active(0).idx).aload(cont2).astore(active(1).idx)
          m.aconst_null.dup.astore(cont1).astore(cont2)
          m.goto(methodStart) //TODO jump directly to the right branch if it can be determined statically
        }
      }

      if(methodEnd != null) m.goto(methodEnd)
    }

    if(bp.cond.isDefined) m.setLabel(branchEnd)
  }

  private def recordStats(loopMarker: VarIdx /* non-null if loopSave */, lastBranch: BranchPlan): Unit = {
    if(config.collectStats) {
      m.aload(ptw).iload(statCellAllocations).iload(statCachedCellReuse).iconst(lastBranch.statSingletonUse)
      if(loopMarker != VarIdx.none) m.aload(loopMarker).ifNonNull.thnElse(m.iconst(1))(m.iconst(0))
      else m.iconst(0)
      m.iconst(lastBranch.statLabelCreate).invoke(ptw_recordStats)
    }
  }

  def emitRule(): Unit = {
    rule.branches.foreach { bp =>
      active(0).reuse = bp.reuse1
      active(1).reuse = bp.reuse2
      reuseBuffers = active.collect { case a if a.reuse != -1 => new WriteBuffer(a) }
      emitBranch(bp)
    }
    if(methodEnd != null) m.setLabel(methodEnd)
    m.return_
  }

  private def createCells(instrs: Vector[CreateInstruction]): Unit = instrs.foreach {
    case GetSingletonCell(idx, sym) =>
      val constr = concreteConstrFor(sym)
      cells(idx) = m.getstatic(cell_singleton(sym)).storeLocal(constr.tpe, s"c$idx")
    case ReuseActiveCell(idx, act) => cells(idx) = active(act).idx
    case NewCell(idx, sym, args) =>
      val constr = concreteConstrFor(sym)

      def loadParams(): Unit = args.foreach {
        case CellIdx(-1, p) => m.aconst_null.iconst(p)
        case CellIdx(c, p) => m.aload(cells(c)).iconst(p)
        case f: FreeIdx => ldBoth(f)
      }

      if(rule.initial || !config.useCellCache) {
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

  // load cached payload value (which is always unboxed) and adapt to class
  private def loadCachedPayload(cached: VarIdx, cls: Class[_]): Unit = {
    if(cls == classOf[Int]) m.iload(cached)
    else {
      m.aload(cached)
      if(cls != classOf[AnyRef]) m.checkcast(tp.o(cls))
    }
  }

  // load temp payload value and adapt to class
  private def loadTempPayload(idx: Int, cls: Class[_]): Unit = {
    if(cls == classOf[Int]) {
      if(temp(idx)._2) m.aload(temp(idx)._1).invoke(intBox_getValue)
      else m.iload(temp(idx)._1)
    } else if(cls == classOf[IntBox] || cls == classOf[RefBox]) m.aload(temp(idx)._1)
    else {
      if(temp(idx)._2) m.aload(temp(idx)._1).invoke(refBox_getValue)
      else m.aload(temp(idx)._1)
      if(cls != classOf[AnyRef]) m.checkcast(tp.o(cls))
    }
  }

  // return VarIdx of unboxed temp var, or None for boxed temp or non-temp arg
  private def unboxedTemp(ea: EmbArg): Option[VarIdx] = ea match {
    case EmbArg.Temp(idx, _) if !temp(idx)._2 => Some(temp(idx)._1)
    case _ => None
  }

  private def loadArg(embArg: EmbArg, cls: Class[_]): Unit = embArg match {
    case EmbArg.Const(i: Int) => m.iconst(i)
    case EmbArg.Const(s: String) => m.ldc(s)
    case EmbArg.Active(i) => loadCachedPayload(cachedPayloads(i), cls)
    case EmbArg.Cell(idx) => m.aload(cells(idx))
    case EmbArg.Temp(idx, _) => loadTempPayload(idx, cls)
  }

  private def computePayloads(bp: BranchPlan): Unit = {
    def setCellValue(embArg: EmbArg.Cell, cls: Class[_]): Unit =
      m.aload(cells(embArg.idx)).swap.invoke(if(cls == classOf[Int]) intBox_setValue else refBox_setValue)
    def loadArgs(pc: PayloadMethodApplication): Unit =
      pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach { case (embArg, cls) => loadArg(embArg, cls) }
    def createLabels(ea: Vector[EmbArg]): Unit = ea.indices.foreach { i =>
      if(i != ea.length-1) m.dup
      unboxedTemp(ea(i)) match {
        case Some(vi) =>
          m.astore(vi)
        case None =>
          loadArg(ea(i), classOf[RefBox])
          m.swap.invoke(refBox_setValue)
      }
    }
    bp.payloadComps.foreach {
      case AllocateTemp(ea, boxed) =>
        temp(ea.idx) = ((ea.pt, boxed) match { //TODO use cached boxes
          case (PayloadType.INT, true) => m.newInitDup(new_IntBoxImpl)().storeLocal(intBoxImplT)
          case (PayloadType.INT, false) => m.local(tp.I)
          case (_, true) => m.newInitDup(new_RefBoxImpl)().storeLocal(refBoxImplT)
          case (_, false) => m.local(tp.c[AnyRef])
        }, boxed)
      case CreateLabelsComp(_, ea) =>
        m.newInitDup(tp.c[AnyRef].constr(tp.m().V))()
        createLabels(ea)
      case ReuseLabelsComp(idx, ea) =>
        m.aload(cells(idx))
        createLabels(ea)
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

  private def checkCond(cond: Option[PayloadComputationPlan], branchEnd: Label): Unit = cond.foreach { case pc: PayloadMethodApplication =>
    callPayloadMethod(m, pc, branchEnd) {
      pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach { case (ea, cls) => loadArg(ea, cls) }
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
}
