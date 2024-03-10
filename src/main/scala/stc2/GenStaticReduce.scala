package de.szeiger.interact.stc2

import de.szeiger.interact._
import de.szeiger.interact.ast.{EmbeddedType, PayloadType, Symbol}
import de.szeiger.interact.codegen.AbstractCodeGen
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

import scala.collection.mutable

class GenStaticReduce(m: MethodDSL, _initialActive: Vector[ActiveCell], level: VarIdx, ptw: VarIdx, rule: RulePlan, codeGen: CodeGen, baseMetricName: String) {
  import codeGen._

  val methodEnd = if(rule.branches.length > 1 || rule.branches.head.branches.nonEmpty) m.newLabel else null
  val methodStart = m.setLabel()
  val (statCellAllocations, statCachedCellReuse) =
    if(config.collectStats) (m.iconst(0).storeLocal(tp.I, "statCellAllocations"), m.iconst(0).storeLocal(tp.I, "statCachedCellReuse"))
    else (VarIdx.none, VarIdx.none)
  // active cells (at least two), updated for the current top-level branch
  val active: Array[ActiveCell] = new Array[ActiveCell](rule.totalActiveCount)
  _initialActive.copyToArray(active)
  // cells and their symbols, updated for the current branches
  val cells = new VarIdxArray(rule.totalCellCount)
  val cellSyms = new Array[Symbol](rule.totalCellCount)
  // cell reuse buffers, updated for the current top-level branch
  val reuseBuffers: Array[WriteBuffer] = new Array(rule.totalActiveCount)
  // payload temp vars and boxed flag, updated for the current branches
  val temp = new Array[(VarIdx, Boolean)](rule.totalTempCount)

  // cached payloads, updated for the current top-level branch
  for(ac <- active if ac != null) cachePayload(ac)
  private def cachePayload(ac: ActiveCell): Unit = {
    if(ac.needsCachedPayload) {
      val name = s"cachedPayload${ac.id}"
      m.lload(ac.vidx).lconst(Allocator.payloadOffset(ac.arity, ac.sym.payloadType)).ladd
      ac.cachedPayload = ac.sym.payloadType match {
        case PayloadType.REF => ???
        case PayloadType.INT => m.invokestatic(allocator_getInt).storeLocal(tp.I, name)
        case PayloadType.LABEL => m.invokestatic(allocator_getLong).storeLocal(tp.J, name)
      }
    }
  }

  // Temporary caches to reduce repeated loads
  private[this] val idxCPCache = mutable.HashMap.empty[FreeIdx, VarIdx]
  private def cachedIdx(indices: FreeIdx*)(f: => Unit): MethodDSL = {
    indices.foreach { idx =>
      ldTaggedCPFRaw(idx)
      idxCPCache.put(idx, m.storeLocal(tp.J, s"cachedIdx_f${idx.active}_${idx.port}"))
    }
    f
    indices.foreach(idxCPCache.remove)
    m
  }
  private[this] val modSymIdCache = mutable.HashMap.empty[FreeIdx, VarIdx]
  private def cachedModSymId(indices: FreeIdx*)(f: => Unit): MethodDSL = {
    indices.foreach { idx =>
      ldModSymIdRaw(idx)
      modSymIdCache.put(idx, m.storeLocal(tp.I, s"cachedModSymId_f${idx.active}_${idx.port}"))
    }
    f
    indices.foreach(modSymIdCache.remove)
    m
  }

  // Local vars to buffer writes to a reused cell
  class WriteBuffer(ac: ActiveCell) {
    val cellIdx: Int = ac.reuse
    private[this] val cps = new VarIdxArray(ac.arity)
    def set(port: Int, ct2: Idx): Unit = {
      ldTaggedCP(ct2)
      cps(port) = m.storeLocal(cellT, s"writeBuffer${ac.id}_${port}")
    }
    def flush(): Unit =
      for(p <- 0 until cps.length if cps(p) != VarIdx.none) {
        m.lload(cells(cellIdx)).lconst(Allocator.auxCPOffset(p)).ladd
        m.lload(cps(p)).invokestatic(allocator_putLong)
      }
  }

  // Cell accessors

  private def ldTaggedCPFRaw(idx: FreeIdx): m.type = {
    m.lload(active(idx.active).vidx)
    Allocator.auxCPOffset(idx.port) match {
      case 0 =>
      case off => m.lconst(off).ladd
    }
    m.invokestatic(allocator_getLong)
  }

  private def ldTaggedCP(idx: Idx): m.type = {
    idx match {
      case idx: FreeIdx =>
        idxCPCache.get(idx) match {
          case Some(v) => m.lload(v)
          case None => ldTaggedCPFRaw(idx)
        }
      case idx: CellIdx =>
        m.lload(cells(idx.idx))
        var l = Allocator.auxCPOffset(idx.port)
        if(idx.port >= 0) l += 2
        if(l != 0) m.lconst(l).ladd
    }
    m
  }

  private def ldUntaggedCP(idx: Idx): m.type = {
    idx match {
      case idx: FreeIdx => ldTaggedCP(idx).lconst(-3L).land
      case idx: CellIdx =>
        m.lload(cells(idx.idx))
        Allocator.auxCPOffset(idx.port) match {
          case 0 =>
          case off => m.lconst(off).ladd
        }
    }
    m
  }

  private def ldFastCP(idx: Idx): m.type = idx match {
    case idx: FreeIdx => ldTaggedCP(idx)
    case idx: CellIdx => ldUntaggedCP(idx)
  }

  // Write to internal cell or reuse buffer for reused cells
  private def setAux(idx: CellIdx, ct2: Idx): Unit =
    reuseBuffers.find(w => w != null && w.cellIdx == idx.idx) match {
      case Some(b) => b.set(idx.port, ct2)
      case None =>
        m.lload(cells(idx.idx))
        m.lconst(Allocator.auxCPOffset(idx.port)).ladd
        ldTaggedCP(ct2).invokestatic(allocator_putLong)
    }

  private[this] def ldModSymIdRaw(idx: FreeIdx): m.type = {
    ldFastCP(idx)
    m.invokestatic(allocator_getInt)
  }

  private[this] def ldModSymId(idx: FreeIdx): m.type = modSymIdCache.get(idx) match {
    case Some(v) => m.iload(v)
    case None => ldModSymIdRaw(idx)
  }

  private[this] def isCellInstance(idx: FreeIdx, sym: Symbol): m.type = // stack: () -> mSymId1, mSymId2 for if_icmpeq
    ldModSymId(idx).iconst((symIds(sym) << 1) | 1)

  private[this] def ifAux(idx: FreeIdx) =
    ldTaggedCP(idx).lconst(2).land.lconst(0).lcmp.if_!=

  def emitBranch(bp: BranchPlan, parents: List[BranchPlan], branchMetricName: String): Unit = {
    //println("***** entering "+bp.show)
    //ShowableNode.print(bp)
    cells.clearFrom(bp.cellOffset)
    bp.cellSyms.copyToArray(cellSyms, bp.cellOffset)
    val branchEnd = m.newLabel

    checkCondition(bp, branchEnd)
    incMetric(s"$branchMetricName", m, ptw)

    val (cont0, cont1, loopCont, tailCont) = {
      val cont0 = m.lconst(0).storeLocal(cellT, "cont0")
      val cont1 = m.lconst(0).storeLocal(cellT, "cont1")
      val l = bp.loopOn0 || bp.loopOn1
      (cont0, cont1, l, !l && bp.branches.isEmpty)
    }
    var firstContCheck = true // skip null check on first attempt
    var tailContUsed = false // set to true on first createCut attempt
    def setCont0(ct1: Idx, ct2: Idx): Unit = {
      ldFastCP(ct1).lstore(cont0)
      ldFastCP(ct2).lstore(cont1)
    }
    def setCont1(ct1: Idx, ct2: Idx): Unit = {
      ldFastCP(ct1).lstore(cont1)
      ldFastCP(ct2).lstore(cont0)
    }
    val tail0Syms = mutable.Set.empty[Symbol]

    createCells(bp.cellCreateInstructions)

    bp.payloadComps.foreach(computePayload(_))

    def ldAndSetAux(ct1: FreeIdx, ct2: Idx) = {
      ldUntaggedCP(ct1)
      ldTaggedCP(ct2)
      m.invokestatic(allocator_putLong)
    }

    def addActive(ct1: Idx, ct2: Idx) = {
      m.aload(ptw)
      ldFastCP(ct1)
      ldFastCP(ct2)
      m.invoke(ptw_addActive)
    }

    def createCut(ct1: Idx, ct2: Idx): Unit = {
      if(!tailCont) addActive(ct1, ct2)
      else {
        ct1 match {
          case ct1: CellIdx => tail0Syms += cellSyms(ct1.idx)
          case _ => tail0Syms += Symbol.NoSymbol
        }
        if(!tailContUsed) {
          tailContUsed = true
          setCont0(ct1, ct2)
        } else m.lload(cont0).lconst(0).lcmp.if_==.thnElse { setCont0(ct1, ct2) } { addActive(ct1, ct2) }
      }
    }

    // Connect remaining wires
    def connectCF(ct1: CellIdx, ct2: FreeIdx): Unit = cachedIdx(ct2) {
      if(ct1.isPrincipal) {
        val mayLoopOn0 = loopCont & ct1.idx == bp.active(0) && bp.loopOn0
        val mayLoopOn1 = loopCont & ct1.idx == bp.active(1) && bp.loopOn1
        cachedModSymId((if(mayLoopOn0 || mayLoopOn1) Seq(ct2) else Nil): _*) {
          ifAux(ct2).thnElse {
            ldAndSetAux(ct2, ct1)
          } {
            if(mayLoopOn0) {
              if(firstContCheck) {
                firstContCheck = false
                isCellInstance(ct2, active(1).sym)
                m.ifI_==.thnElse { setCont0(ct1, ct2) } { createCut(ct1, ct2) }
              } else {
                m.lload(cont0).lconst(0).lcmp.if_==.and {
                  isCellInstance(ct2, active(1).sym)
                }.ifI_==.thnElse { setCont0(ct1, ct2) } { createCut(ct1, ct2) }
              }
            } else if(mayLoopOn1) {
              if(firstContCheck) {
                firstContCheck = false
                isCellInstance(ct2, active(0).sym)
                m.ifI_==.thnElse { setCont1(ct1, ct2) } { createCut(ct1, ct2) }
              } else {
                m.lload(cont0).lconst(0).lcmp.if_==.and {
                  isCellInstance(ct2, active(0).sym)
                }.ifI_==.thnElse { setCont1(ct1, ct2) } { createCut(ct1, ct2) }
              }
            } else {
              createCut(ct1, ct2)
            }
          }
        }
      } else {
        setAux(ct1, ct2)
        ifAux(ct2).thn {
          ldAndSetAux(ct2, ct1)
        }
      }
    }
    def connectFF(ct1: FreeIdx, ct2: FreeIdx): Unit = cachedIdx(ct1, ct2) {
      ifAux(ct1).thnElse {
        ldAndSetAux(ct1, ct2)
        ifAux(ct2).thn {
          ldAndSetAux(ct2, ct1)
        }
      } {
        ifAux(ct2).thnElse {
          ldAndSetAux(ct2, ct1)
        } {
          createCut(ct1, ct2)
        }
      }
    }
    def connectCC(ct1: CellIdx, ct2: CellIdx): Unit = {
      if(ct1.isAux && !bp.cellPortsConnected.contains(ct1))
        setAux(ct1, ct2)
      if(ct2.isAux && !bp.cellPortsConnected.contains(ct2))
        setAux(ct2, ct1)
      if(ct1.isPrincipal && ct2.isPrincipal)
        createCut(ct1, ct2)
    }
    bp.sortedConns.foreach {
      case Connection(i1: FreeIdx, i2: FreeIdx) => connectFF(i1, i2)
      case Connection(i1: FreeIdx, i2: CellIdx) => connectCF(i2, i1)
      case Connection(i1: CellIdx, i2: FreeIdx) => connectCF(i1, i2)
      case Connection(i1: CellIdx, i2: CellIdx) => connectCC(i1, i2)
    }

    if(bp.branches.nonEmpty)
      bp.branches.zipWithIndex.foreach { case (b, i) => emitBranch(b, bp :: parents, s"$branchMetricName.$i") }
    else {
      for(w <- reuseBuffers if w != null) w.flush()

      def singleDispatchTail = tail0Syms.size == 1 && tail0Syms.head.isDefined
      recordStats(cont0, bp, parents, loopCont, tailCont, singleDispatchTail, level)

      if(loopCont) {
        m.lload(cont0).lconst(0).lcmp.if_!=.thn {
          m.lload(cont0).lstore(active(0).vidx).lload(cont1).lstore(active(1).vidx)
          m.goto(methodStart) //TODO jump directly to the right branch if it can be determined statically
        }
      } else if(tailContUsed) {
        m.lload(cont0).lconst(0).lcmp.if_!=.thn {
          m.iload(level).if_!=.thnElse {
            m.iinc(level, -1)
            m.lload(cont0).lload(cont1).iload(level).aload(ptw)
            if(singleDispatchTail) {
              m.invokestatic(metaClass_reduce(tail0Syms.head))
            } else {
              m.invokestatic(dispatch_staticReduce)
            }
          } {
            m.aload(ptw).lload(cont0).lload(cont1).invoke(ptw_addActive)
          }
        }
      }

      if(methodEnd != null) m.goto(methodEnd)
    }

    if(bp.cond.isDefined) m.setLabel(branchEnd)
  }

  private def recordStats(contMarker: VarIdx /* defined if loopSave */, lastBranch: BranchPlan, parents: List[BranchPlan],
    loopCont: Boolean, tailCont: Boolean, singleDispatchTail: Boolean, level: VarIdx): Unit = {
    if(config.collectStats) {
      m.aload(ptw).iconst((lastBranch :: parents).map(_.statSteps).sum)
      m.iload(statCellAllocations).iload(statCachedCellReuse).iconst(lastBranch.statSingletonUse)
      if(loopCont) m.lload(contMarker).lconst(0).lcmp.if_!=.thnElse(m.iconst(1))(m.iconst(0))
      else m.iconst(0)
      if(tailCont) {
        m.iload(level).if_==.thnElse {
          m.iconst(0).iconst(0)
        } {
          m.lload(contMarker).lconst(0).lcmp.if_!=.thnElse {
            m.iconst(1).iconst(if(singleDispatchTail) 1 else 0)
          } {
            m.iconst(0).iconst(0)
          }
        }
      } else m.iconst(0).iconst(0)
      m.iconst(lastBranch.statLabelCreate).invoke(ptw_recordStats)
    }
  }

  def emitRule(): Unit = {
    rule.branches.zipWithIndex.foreach { case (bp, branchIdx) =>
      active(0).reuse = bp.active(0)
      active(1).reuse = bp.active(1)
      for(i <- 2 until active.length) {
        active(i) = null
      }
      for(i <- active.indices)
        reuseBuffers(i) = if(active(i) == null || active(i).reuse == -1) null else new WriteBuffer(active(i))
      emitBranch(bp, Nil, s"$baseMetricName#$branchIdx")
    }
    if(methodEnd != null) m.setLabel(methodEnd)
    m.return_
  }

  private def createCells(instrs: Vector[CreateInstruction]): Unit = {
    val singletonCache = mutable.HashMap.empty[Symbol, VarIdx]
    instrs.foreach {
      case GetSingletonCell(idx, sym) =>
        cells(idx) = active.find(_.sym == sym) match {
          case Some(a) => a.vidx
          case None =>
            singletonCache.getOrElseUpdate(sym, {
              m.aload(ptw).iconst(symIds(sym)).invoke(ptw_getSingleton).storeLocal(cellT, s"cell${idx}_singleton_${AbstractCodeGen.encodeName(sym)}")
            })
        }
      case ReuseActiveCell(idx, act, sym) =>
        assert(symIds(sym) >= 0)
        cells(idx) = active(act).vidx
        if(sym != active(act).sym)
          m.lload(active(act).vidx).iconst((symIds(sym) << 1) | 1).invokestatic(allocator_putInt)
      case NewCell(idx, sym, args) =>
        m.aload(ptw).iconst(Allocator.cellSize(sym.arity, sym.payloadType)).invoke(ptw_allocCell)
        assert(symIds(sym) >= 0)
        m.dup2.iconst((symIds(sym) << 1) | 1).invokestatic(allocator_putInt)
        args.zipWithIndex.foreach {
          case (CellIdx(-1, _), _) => // principal, nothing to connect
          case (_: FreeIdx, _) => // done later when connecting opposite direction
          case (idx, p1) =>
            m.dup2.lconst(Allocator.auxCPOffset(p1)).ladd
            ldTaggedCP(idx).invokestatic(allocator_putLong)
        }
        if(config.collectStats) m.iinc(statCellAllocations)
        cells(idx) = m.storeLocal(cellT, s"cell${idx}_${AbstractCodeGen.encodeName(sym)}")
    }
  }

  // load cached payload value (which is always unboxed) and adapt to class
  private def loadCachedPayload(cached: VarIdx, cls: Class[_]): Unit = {
    if(cls == classOf[Int]) m.iload(cached)
    else if(cls == classOf[Long]) m.lload(cached)
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
    }
    else if(cls == classOf[Long]) {
      if(temp(idx)._2) m.aload(temp(idx)._1).invoke(longBox_getValue)
      else m.lload(temp(idx)._1)
    }
    else if(cls == classOf[IntBox] || cls == classOf[LongBox] || cls == classOf[RefBox]) m.aload(temp(idx)._1)
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
    case EmbArg.Active(i) => loadCachedPayload(active(i).cachedPayload, cls)
    case EmbArg.Cell(idx) => ??? //m.aload(cells(idx))
    case EmbArg.Temp(idx, _) => loadTempPayload(idx, cls)
  }

  private def writeToArg(ea: EmbArg, boxCls: Class[_])(loadSource: => Unit): Unit = ea match {
    case EmbArg.Cell(idx) =>
      m.lload(cells(idx)).lconst(Allocator.payloadOffset(cellSyms(idx).arity, cellSyms(idx).payloadType)).ladd
      loadSource
      if(boxCls == classOf[LongBox]) m.invokestatic(allocator_putLong)
      else if(boxCls == classOf[IntBox]) m.invokestatic(allocator_putInt)
      else ???
    case _ =>
      loadArg(ea, boxCls)
      loadSource
      m.invoke(refBox_setValue)
  }

  private def setLabels(eas: Vector[EmbArg]): Unit = {
    val l = m.storeLocal(tp.J)
    eas.foreach { ea =>
      unboxedTemp(ea) match {
        case Some(vi) =>
          m.lload(l)
          m.lstore(vi)
        case None =>
          writeToArg(ea, classOf[LongBox])(m.lload(l))
      }
    }
  }

  private def checkCondition(bp: BranchPlan, endTarget: Label) = {
    bp.cond.foreach {
      case CheckPrincipal(wire, sym, activeIdx) =>
        ifAux(wire).jump(endTarget)
        isCellInstance(wire, sym).ifI_!=.thnElse {
          m.goto(endTarget)
        } {
          ldUntaggedCP(wire)
          val vidx = m.storeLocal(cellT, s"active$activeIdx")
          val ac = new ActiveCell(activeIdx, vidx, sym, sym.arity, bp.needsCachedPayloads(activeIdx))
          ac.reuse = bp.active(activeIdx)
          active(activeIdx) = ac
          reuseBuffers(activeIdx) = if(ac.reuse == -1) null else new WriteBuffer(ac)
          cachePayload(ac)
        }
      case pc =>
        computePayload(pc, endTarget)
    }
  }

  private def computePayload(pc: PayloadComputationPlan, elseTarget: Label = null): Unit = pc match {
    case AllocateTemp(ea, boxed) =>
      assert(elseTarget == null)
      val name = s"temp${ea.idx}"
      temp(ea.idx) = ((ea.pt, boxed) match { //TODO use cached boxes
        case (PayloadType.INT, true) => m.newInitDup(new_IntBoxImpl)().storeLocal(intBoxImplT, name)
        case (PayloadType.INT, false) => m.local(tp.I, name)
        case (_, true) => m.newInitDup(new_RefBoxImpl)().storeLocal(refBoxImplT, name)
        case (_, false) => m.local(tp.c[AnyRef], name)
      }, boxed)
    case CreateLabelsComp(_, ea) =>
      assert(elseTarget == null)
      m.aload(ptw).invoke(ptw_newLabel)
      setLabels(ea)
    case ReuseLabelsComp(idx, ea) => // can't mix reuse with non-address labels
      assert(elseTarget == null)
      //m.lload(cells(idx))
      m.aload(ptw).invoke(ptw_newLabel)
      setLabels(ea)
    case pc: PayloadMethodApplication =>
      if(elseTarget == null) assert(pc.jMethod.getReturnType == Void.TYPE)
      else assert(pc.jMethod.getReturnType == java.lang.Boolean.TYPE)
      callPayloadMethod(m, pc, elseTarget)
    case pc: PayloadAssignment =>
      assert(elseTarget == null)
      assert(pc.payloadType.isDefined)
      if(pc.payloadType == PayloadType.INT) {
        unboxedTemp(pc.targetIdx) match {
          case Some(vi) =>
            loadArg(pc.sourceIdx, classOf[Int])
            m.istore(vi)
          case None =>
            writeToArg(pc.targetIdx, classOf[IntBox])(loadArg(pc.sourceIdx, classOf[Int]))
        }
      } else if(pc.payloadType == PayloadType.LABEL) {
        unboxedTemp(pc.targetIdx) match {
          case Some(vi) =>
            loadArg(pc.sourceIdx, classOf[Long])
            m.lstore(vi)
          case None =>
            writeToArg(pc.targetIdx, classOf[LongBox])(loadArg(pc.sourceIdx, classOf[Long]))
        }
      } else {
        ???
      }
    case PayloadMethodApplicationWithReturn(method, retIdx) =>
      assert(elseTarget == null)
      unboxedTemp(retIdx) match {
        case Some(vi) =>
          callPayloadMethod(m, method, null)
          if(method.embTp.ret == EmbeddedType.PayloadInt) m.istore(vi)
          else m.astore(vi)
        case None =>
          if(method.embTp.ret == EmbeddedType.PayloadInt)
            writeToArg(retIdx, classOf[IntBox])(callPayloadMethod(m, method, null))
          else if(method.embTp.ret == EmbeddedType.PayloadLabel)
            writeToArg(retIdx, classOf[LongBox])(callPayloadMethod(m, method, null))
          else ???
      }
  }

  private def callPayloadMethod(m: MethodDSL, pc: PayloadMethodApplication, elseTarget: Label): Unit = {
    def loadArgs = pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach { case (embArg, cls) => loadArg(embArg, cls) }
    val RuntimeCls = classOf[Runtime.type].getName
    (pc.jMethod.getDeclaringClass.getName, pc.jMethod.getName, pc.embTp.args) match {
      case (RuntimeCls, "eq", Vector((EmbeddedType.PayloadInt, false), (EmbeddedType.PayloadInt, false))) if elseTarget != null =>
        loadArgs
        m.ifI_!=.jump(elseTarget)
      case (RuntimeCls, "eqLabel", Vector((EmbeddedType.PayloadLabel, false), (EmbeddedType.PayloadLabel, false))) if elseTarget != null =>
        pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach { case (embArg, _) => loadArg(embArg, classOf[Long]) }
        m.lcmp.if_!=.jump(elseTarget)
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
