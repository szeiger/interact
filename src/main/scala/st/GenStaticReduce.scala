package de.szeiger.interact.st

import de.szeiger.interact.{BranchPlan, CellIdx, Config, Connection, CreateInstruction, EmbArg, FreeIdx, GetSingletonCell, Idx, IntBox, NewCell, PayloadAssignment, PayloadComputation, PayloadMethodApplication, PayloadMethodApplicationWithReturn, RefBox, Reuse1, Reuse2, RulePlan, Runtime}
import de.szeiger.interact.ast.{EmbeddedType, PayloadType, Symbol}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

class GenStaticReduce(m: MethodDSL, cLeft: VarIdx, cRight: VarIdx, cLeftTp: Owner, cRightTp: Owner, ptw: VarIdx,
  rule: RulePlan, defs: Defs, config: Config, common: Set[Symbol]) {
  import defs._

  val methodEnd = if(rule.branches.length > 1) m.newLabel else null
  val methodStart = m.setLabel()
  val statCellAllocations, statCachedCellReuse = if(config.collectStats) m.iconst(0).storeLocal(tp.I) else VarIdx.none
  // cells and their symbols, updated for the current branches
  val cells = new VarIdxArray(rule.totalCellCount)
  val cellSyms = new Array[Symbol](rule.totalCellCount)
  // cell reuse buffers, updated for the current top-level branch
  var reuse1Buffer: WriteBuffer = _
  var reuse2Buffer: WriteBuffer = _
  // payload temp vars and types, updated for the current branches
  val temp = new VarIdxArray(rule.totalTempCount)
  val tempPts = new Array[(PayloadType, Boolean)](rule.totalTempCount)
  // cached payloads, shared between all branches
  val (cachedPayload1, cachedPayload2) = {
    def cache(cell: VarIdx, pt: PayloadType): VarIdx = pt match {
      case PayloadType.VOID => VarIdx.none
      case PayloadType.INT => m.aload(cell).invoke(intBox_getValue).storeLocal(tp.I)
      case _ => m.aload(cell).invoke(refBox_getValue).storeLocal(tp.c[AnyRef])
    }
    (cache(cLeft, rule.sym1.payloadType), cache(cRight, rule.sym2.payloadType))
  }

  // Local vars to buffer writes to a reused cell
  class WriteBuffer(val cellIdx: Int, arity: Int, sym: Symbol) {
    private[this] val buf = new VarIdxArray(arity*2)
    def set(port: Int, ct2: Idx): Unit = {
      ldBoth(ct2)
      buf(port*2+1) = m.storeLocal(tp.I)
      buf(port*2) = m.storeLocal(cellT)
    }
    def flush(): Unit =
      for(p <- 0 until buf.length/2) {
        if(buf(p*2) != VarIdx.none)
          m.aload(cells(cellIdx)).aload(buf(p*2)).putfield(cell_acell(sym, p))
        if(buf(p*2+1) != VarIdx.none)
          m.aload(cells(cellIdx)).iload(buf(p*2+1)).putfield(cell_aport(sym, p))
      }
  }

  // Cell accessors
  private def ldCell(idx: Idx) = idx match {
    case FreeIdx(rhs, p) =>
      m.aload(if(rhs) cRight else cLeft)
      if(rule.initial) m.iconst(p).invoke(cell_auxCell)
      else m.getfield(cell_acell(if(rhs) rule.sym2 else rule.sym1, p))
    case CellIdx(i, _) => m.aload(cells(i))
  }
  private def ldPort(idx: Idx) = idx match {
    case FreeIdx(rhs, p) =>
      m.aload(if(rhs) cRight else cLeft)
      if(rule.initial) m.iconst(p).invoke(cell_auxPort)
      else m.getfield(cell_aport(if(rhs) rule.sym2 else rule.sym1, p))
    case CellIdx(_, p) => m.iconst(p)
  }
  private def ldBoth(idx: Idx) = { ldCell(idx); ldPort(idx) }

  // Write to internal cell or reuse buffer for reused cells
  private def setAux(idx: CellIdx, ct2: Idx, setPort: Boolean = true): Unit = {
    val sym = cellSyms(idx.idx)
    if(reuse1Buffer != null && idx.idx == reuse1Buffer.cellIdx) reuse1Buffer.set(idx.port, ct2)
    else if(reuse2Buffer != null && idx.idx == reuse2Buffer.cellIdx) reuse2Buffer.set(idx.port, ct2)
    else {
      m.aload(cells(idx.idx))
      if(setPort) m.dup
      ldCell(ct2).putfield(cell_acell(sym, idx.port))
      if(setPort) ldPort(ct2).putfield(cell_aport(sym, idx.port))
    }
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
        val cont1 = m.aconst_null.storeLocal(concreteCellTFor(rule.sym1))
        val cont2 = m.aconst_null.storeLocal(concreteCellTFor(rule.sym2))
        (cont1, cont2)
      } else (VarIdx.none, VarIdx.none)
    }

    createCells(bp.cellCreateInstructions)

    computePayloads(bp)

    // Connect remaining wires
    def connectCF(ct1: CellIdx, ct2: FreeIdx): Unit = {
      if(bp.isReuse(ct1) && ct1.isAux)
        setAux(ct1, ct2)
      if(ct1.isPrincipal) {
        ldPort(ct2).if_>=.thnElse {
          ldBoth(ct2); ldBoth(ct1).invoke(cell_setAux)
        } {
          if(ct1.idx == bp.reuse1 && bp.loopOn1) {
            m.aload(cont1).ifNull.and {
              ldCell(ct2).instanceof(concreteCellTFor(rule.sym2))
            }.if_!=.thnElse {
              ldCell(ct1).astore(cont1)
              ldCell(ct2).checkcast(concreteCellTFor(rule.sym2)).astore(cont2)
            } {
              createCut(ct1, ct2)
            }
          } else if(ct1.idx == bp.reuse2 && bp.loopOn2) {
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

    if(bp.branches.isEmpty) {
      if(reuse1Buffer != null) reuse1Buffer.flush()
      if(reuse2Buffer != null) reuse2Buffer.flush()

      if(config.useCellCache && !rule.initial) {
        if(bp.reuse1 == -1) m.aload(cLeft).invokestatic(cellCache_set(rule.sym1))
        if(bp.reuse2 == -1) m.aload(cRight).invokestatic(cellCache_set(rule.sym2))
      }

      recordStats(cont1, bp)

      if(cont1 != VarIdx.none) {
        m.aload(cont1).ifNonNull.thn {
          m.aload(cont1).astore(cLeft).aload(cont2).astore(cRight)
          m.aconst_null.dup.astore(cont1).astore(cont2)
          m.goto(methodStart) //TODO jump directly to the right branch if it can be determined statically
        }
      }

      if(methodEnd != null) m.goto(methodEnd)
    } else {
      bp.branches.foreach(b => emitBranch(b))
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
      reuse1Buffer = if(bp.reuse1 != -1) new WriteBuffer(bp.reuse1, rule.arity1, rule.sym1) else null
      reuse2Buffer = if(bp.reuse2 != -1) new WriteBuffer(bp.reuse2, rule.arity2, rule.sym2) else null
      emitBranch(bp)
    }
    if(methodEnd != null) m.setLabel(methodEnd)
    m.return_
  }

  private def createCells(instrs: Vector[CreateInstruction]): Unit = instrs.foreach {
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
      if(tempPts(idx)._2) m.aload(temp(idx)).invoke(intBox_getValue)
      else m.iload(temp(idx))
    } else if(cls == classOf[IntBox] || cls == classOf[RefBox]) m.aload(temp(idx))
    else {
      if(tempPts(idx)._2) m.aload(temp(idx)).invoke(refBox_getValue)
      else m.aload(temp(idx))
      if(cls != classOf[AnyRef]) m.checkcast(tp.o(cls))
    }
  }

  // return VarIdx of unboxed temp var, or None for boxed temp or non-temp arg
  private def unboxedTemp(ea: EmbArg): Option[VarIdx] = ea match {
    case EmbArg.Temp(idx, _) if !tempPts(idx)._2 => Some(temp(idx))
    case _ => None
  }

  private def loadArg(embArg: EmbArg, cls: Class[_]): Unit = embArg match {
    case EmbArg.Const(i: Int) => m.iconst(i)
    case EmbArg.Const(s: String) => m.ldc(s)
    case EmbArg.Left => loadCachedPayload(cachedPayload1, cls)
    case EmbArg.Right => loadCachedPayload(cachedPayload2, cls)
    case EmbArg.Cell(idx) => m.aload(cells(idx))
    case EmbArg.Temp(idx, _) => loadTempPayload(idx, cls)
  }

  private def computePayloads(bp: BranchPlan): Unit = {
    bp.payloadTemp.zipWithIndex.foreach { case (pt, idx) =>
      tempPts(idx + bp.tempOffset) = (pt)
      temp(idx + bp.tempOffset) = pt match {
        //TODO use cached boxes
        case (PayloadType.INT, true) => m.newInitDup(new_IntBoxImpl)().storeLocal(intBoxImplT)
        case (PayloadType.INT, false) => m.local(tp.I)
        case (_, true) => m.newInitDup(new_RefBoxImpl)().storeLocal(refBoxImplT)
        case (_, false) => m.local(tp.c[AnyRef])
      }
    }
    bp.createLabelComps.foreach { case (pc, idx) =>
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
    def setCellValue(embArg: EmbArg.Cell, cls: Class[_]): Unit =
      m.aload(cells(embArg.idx)).swap.invoke(if(cls == classOf[Int]) intBox_setValue else refBox_setValue)
    def loadArgs(pc: PayloadMethodApplication): Unit =
      pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach { case (embArg, cls) => loadArg(embArg, cls) }
    bp.otherPayloadComps.foreach {
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

  private def checkCond(cond: Option[PayloadComputation], branchEnd: Label): Unit = {
    def adaptPayloadFromCell(cell: VarIdx, cellTp: Owner, cls: Class[_]): Unit = {
      m.aload(cell)
      if(cls == classOf[Int]) m.invoke(intBox_getValue, cellTp)
      else if(cls == classOf[AnyRef]) m.invoke(refBox_getValue, cellTp)
      else m.invoke(refBox_getValue, cellTp).checkcast(tp.o(cls))
    }
    cond.foreach { case pc: PayloadMethodApplication =>
      assert(pc.jMethod.getReturnType == classOf[Boolean])
      callPayloadMethod(m, pc, branchEnd) {
        pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach {
          case (EmbArg.Const(i: Int), _) => m.iconst(i)
          case (EmbArg.Const(s: String), _) => m.ldc(s)
          case (EmbArg.Left, cls) => adaptPayloadFromCell(cLeft, cLeftTp, cls)
          case (EmbArg.Right, cls) => adaptPayloadFromCell(cRight, cRightTp, cls)
          case (EmbArg.Temp(idx, _), cls) => loadTempPayload(idx, cls)
        }
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
}
