package de.szeiger.interact.stc2

import de.szeiger.interact._
import de.szeiger.interact.ast.{EmbeddedType, PayloadType, Symbol}
import de.szeiger.interact.codegen.AbstractCodeGen
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import de.szeiger.interact.offheap.Allocator
import org.objectweb.asm.Label

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

import Interpreter._

class GenStaticReduce(m: MethodDSL, _initialActive: Vector[ActiveCell], level: VarIdx, ptw: VarIdx, rule: RulePlan,
  implicit val codeGen: CodeGen, baseMetricName: String) {
  import codeGen._

  val methodStart = m.setLabel()
  val (statCellAllocations, statUnboxedAllocations, statProxyAllocations, statCachedCellReuse) =
    if(config.collectStats) (m.iconst(0).storeLocal(tp.I, "statCellAllocations"), m.iconst(0).storeLocal(tp.I, "statUnboxedAllocations"), m.iconst(0).storeLocal(tp.I, "statProxyAllocations"), m.iconst(0).storeLocal(tp.I, "statCachedCellReuse"))
    else (VarIdx.none, VarIdx.none, VarIdx.none, VarIdx.none)
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
      val name = s"payload${ac.id}${ac.sym.payloadType}_${ac.encName}"
      ac.sym.payloadType match {
        case PayloadType.REF =>
          m.aload(ptw).lload(ac.vidx).invoke(ptw_getProxyPage)
          ac.cachedPayloadProxyPage = m.dup.storeLocal(tp.Object, s"${name}PP")
          m.lload(ac.vidx).lconst(Allocator.proxyElemOffset).ladd.invokestatic(allocator_getInt)
          ac.cachedPayloadProxyPageOffset = m.dup.storeLocal(tp.I, s"${name}PPOff")
          ac.cachedPayload = m.i2l.invokestatic(allocator_getObject).storeLocal(tp.Object, name)
        case pt =>
          val p = PTOps(m, pt)
          if(ac.unboxed) p.extractUnboxed { m.lload(ac.vidx) }
          else p.getCellPayload(ptw, ac.arity) { m.lload(ac.vidx) }
          ac.cachedPayload = m.storeLocal(p.desc.unboxedT, name)
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

  // Local vars to buffer writes to a reused cell
  class WriteBuffer(ac: ActiveCell) {
    val cellIdx: Int = ac.reuse
    private[this] val free = new VarIdxArray(ac.arity)
    private[this] val cell = new Array[CellIdx](ac.arity)
    def set(port: Int, ct2: Idx): Unit = ct2 match {
      case ct2: CellIdx => cell(port) = ct2
      case _ =>
        ldTaggedCP(ct2)
        free(port) = m.storeLocal(cellT, s"writeBuffer${ac.id}_${port}")
    }
    def flush(): Unit =
      for(p <- 0 until free.length if free(p) != VarIdx.none || cell(p) != null) {
        m.lload(cells(cellIdx)).lconst(auxPtrOffset(p)).ladd
        if(free(p) != VarIdx.none) m.lload(free(p)) else ldTaggedCP(cell(p))
        m.invokestatic(allocator_putLong)
      }
  }

  // Cell accessors

  private def ldTaggedCPFRaw(idx: FreeIdx): m.type = {
    m.lload(active(idx.active).vidx)
    auxPtrOffset(idx.port) match {
      case 0 =>
      case off => m.lconst(off).ladd
    }
    m.invokestatic(allocator_getLong)
  }

  private def ldTaggedCP(idx: Idx): Option[VarIdx] = {
    idx match {
      case idx: FreeIdx =>
        idxCPCache.get(idx) match {
          case Some(v) => m.lload(v); Some(v)
          case None => ldTaggedCPFRaw(idx); None
        }
      case idx: CellIdx =>
        if(cells(idx.idx).isEmpty) {
          val sym = cellSyms(idx.idx)
          assert(shouldUnbox(sym) && idx.port == -1)
          if(sym.payloadType == PayloadType.VOID) {
            m.lconst(mkUnboxed(symIds(sym)).toLong & 0xffffffffL)
          } else {
            val ac = active.find(a => a != null && a.reuse == idx.idx).get
            m.lload(ac.vidx)
          }
          None
        } else {
          m.lload(cells(idx.idx))
          var l = auxPtrOffset(idx.port)
          if(idx.port >= 0) l += TAG_AUX_PTR
          if(l != 0) {
            m.lconst(l).ladd
            None
          } else Some(cells(idx.idx))
        }
    }
  }

  private def ldUntaggedCP(idx: Idx): Option[VarIdx] = {
    idx match {
      case idx: FreeIdx =>
        ldTaggedCP(idx)
        m.lconst(ADDRMASK).land
        None
      case idx: CellIdx =>
        if(cells(idx.idx).isEmpty) {
          ldTaggedCP(idx)
        } else {
          m.lload(cells(idx.idx))
          auxPtrOffset(idx.port) match {
            case 0 => Some(cells(idx.idx))
            case off => m.lconst(off).ladd; None
          }
        }
    }
  }

  private def ldFastCP(idx: Idx): Option[VarIdx] = idx match {
    case idx: FreeIdx => ldTaggedCP(idx)
    case idx: CellIdx => ldUntaggedCP(idx)
  }

  // Write to internal cell or reuse buffer for reused cells
  private def setAux(idx: CellIdx, ct2: Idx): Unit =
    reuseBuffers.find(w => w != null && w.cellIdx == idx.idx) match {
      case Some(b) => b.set(idx.port, ct2)
      case None =>
        m.lload(cells(idx.idx))
        m.lconst(auxPtrOffset(idx.port)).ladd
        ldTaggedCP(ct2)
        m.invokestatic(allocator_putLong)
    }

  private[this] def ifBoxed(idx: FreeIdx, sym: Symbol): ThenDSL = {
    // must have already checked ifPrincipal!
    ldTaggedCP(idx)
    m.invokestatic(allocator_getInt)
    m.iconst(mkHeader(symIds(sym))).ifI_==
  }

  private[this] def ifUnboxed(idx: FreeIdx, sym: Symbol): ThenDSL = {
    ldTaggedCP(idx)
    m.lconst(0xffffffffL).land.l2i.iconst(mkUnboxed(symIds(sym))).ifI_==
  }

  private[this] def ifAux(idx: FreeIdx): ThenDSL = {
    ldTaggedCP(idx)
    m.lconst(TAGMASK).land.lconst(TAG_AUX_PTR).lcmp.if_==
  }

  private[this] def ifPrincipal(idx: FreeIdx): ThenDSL = {
    ldTaggedCP(idx)
    m.lconst(TAGMASK).land.l2i.if_==
  }

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
      (cont0, cont1, l, !l && bp.branches.isEmpty && !rule.initial)
    }
    val cont0Options, cont1Options = mutable.HashSet.empty[VarIdx]
    var firstContCheck = true // skip null check on first attempt
    var tailContUsed = false // set to true on first createCut attempt
    var tailContUsedUnconditionally: Option[(Symbol, Symbol)] = None // set on first createCut attempt with 2 CellIdx
    def setCont(ct1: Idx, ct2: Idx): Unit = {
      ldFastCP(ct1) match {
        case Some(v) => cont0Options += v
        case None => cont0Options += VarIdx.none
      }
      m.lstore(cont0)
      ldFastCP(ct2) match {
        case Some(v) => cont1Options += v
        case None => cont1Options += VarIdx.none
      }
      m.lstore(cont1)
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
        val uncond = ct1 match {
          case ct1: CellIdx =>
            tail0Syms += cellSyms(ct1.idx)
            ct2 match {
              case ct2: CellIdx => Some((cellSyms(ct1.idx), cellSyms(ct2.idx)))
              case _ => None
            }
          case _ =>
            tail0Syms += Symbol.NoSymbol
            None
        }
        if(!tailContUsed) {
          tailContUsed = true
          tailContUsedUnconditionally = uncond
          setCont(ct1, ct2)
        } else if(tailContUsedUnconditionally.isDefined) {
          addActive(ct1, ct2)
        } else {
          m.lload(cont0).lconst(0).lcmp.if_==.thnElse { setCont(ct1, ct2) } { addActive(ct1, ct2) }
        }
      }
    }

    // Connect remaining wires
    def connectCF(ct1: CellIdx, ct2: FreeIdx): Unit = cachedIdx(ct2) {
      if(ct1.isPrincipal) {
        val mayLoopOn0 = loopCont & ct1.idx == bp.active(0) && bp.loopOn0
        val mayLoopOn1 = loopCont & ct1.idx == bp.active(1) && bp.loopOn1
        ifAux(ct2).thnElse {
          ldAndSetAux(ct2, ct1)
        } {
          if(mayLoopOn0 || mayLoopOn1) {
            val (sym, ctA, ctB) = if(mayLoopOn0) (active(1).sym, ct1, ct2) else (active(0).sym, ct2, ct1)
            val lCreateCut, lEnd = m.newLabel
            if(firstContCheck) firstContCheck = false
            else m.lload(cont0).lconst(0).lcmp.if_!=.jump(lCreateCut)
            if(shouldUnbox(sym))
              ifUnboxed(ct2, sym).not.jump(lCreateCut)
            else {
              if(config.unboxedPrimitives) ifPrincipal(ct2).not.jump(lCreateCut)
              ifBoxed(ct2, sym).not.jump(lCreateCut)
            }
            setCont(ctA, ctB)
            m.goto(lEnd)
            m.setLabel(lCreateCut)
            createCut(ct1, ct2)
            m.setLabel(lEnd)
          } else {
            createCut(ct1, ct2)
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
      for(ac <- active if ac != null && ac.reuse == -1 && !ac.sym.isSingleton && !ac.unboxed) {
        m.aload(ptw).lload(ac.vidx)
        val sz = cellSize(ac.arity, ac.sym.payloadType)
        ac.sym.payloadType match {
          case PayloadType.REF =>
            if(specializedCellAllocSizes.contains(sz)) m.invoke(ptw_freeProxiedSpec(sz))
            else m.iconst(sz).invoke(ptw_freeProxied)
          case _ =>
            if(specializedCellAllocSizes.contains(sz)) m.invoke(ptw_freeSpec(sz))
            else m.iconst(sz).invoke(ptw_freeCell)
        }
      }

      def singleDispatchTail = tail0Syms.size == 1 && tail0Syms.head.isDefined
      //recordStats(cont0, bp, parents, loopCont, tailCont, singleDispatchTail, level)
      recordSteps(bp, parents)

      if(loopCont) {
        m.lload(cont0).lconst(0).lcmp.if_!=.thn {
          recordDispatch(1, 0, 0)
          if(cont0Options != mutable.Set(active(0).vidx)) m.lload(cont0).lstore(active(0).vidx)
          if(cont1Options != mutable.Set(active(1).vidx)) m.lload(cont1).lstore(active(1).vidx)
          m.goto(methodStart) //TODO jump directly to the right branch if it can be determined statically
        }
      } else if(tailContUsed) {
        if(tailContUsedUnconditionally.isDefined) {
          val (cont0Sym, cont1Sym) = tailContUsedUnconditionally.get
          if(cont0Sym == active(0).sym && cont1Sym == active(1).sym) {
            recordDispatch(1, 0, 0)
            if(cont0 != active(0).vidx) m.lload(cont0).lstore(active(0).vidx)
            if(cont1 != active(1).vidx) m.lload(cont1).lstore(active(1).vidx)
            m.goto(methodStart)
          } else if(cont0Sym == active(1).sym && cont1Sym == active(0).sym) {
            recordDispatch(1, 0, 0)
            if(cont0 != active(1).vidx) m.lload(cont0).lstore(active(1).vidx)
            if(cont1 != active(0).vidx) m.lload(cont1).lstore(active(0).vidx)
            m.goto(methodStart)
          } else {
            recordDispatch(0, 1, 1)
            m.lload(cont0).lload(cont1).iload(level).aload(ptw)
            m.invokestatic(metaClass_reduce(cont0Sym))
          }
        } else m.lload(cont0).lconst(0).lcmp.if_!=.thn {
          m.iload(level).if_!=.thnElse {
            m.iinc(level, -1)
            m.lload(cont0).lload(cont1).iload(level).aload(ptw)
            if(singleDispatchTail) {
              recordDispatch(0, 1, 1)
              m.invokestatic(metaClass_reduce(tail0Syms.head))
            } else {
              recordDispatch(0, 1, 0)
              m.invokestatic(generatedDispatch_staticReduce)
            }
          } {
            m.aload(ptw).lload(cont0).lload(cont1).invoke(ptw_addActive)
          }
        }
      }

      m.return_
    }

    if(bp.cond.isDefined) m.setLabel(branchEnd)
  }

  private def recordSteps(lastBranch: BranchPlan, parents: List[BranchPlan]): Unit = {
    if(config.collectStats) {
      m.aload(ptw).iconst((lastBranch :: parents).map(_.statSteps).sum)
      m.iload(statCellAllocations).iload(statProxyAllocations).iload(statCachedCellReuse)
      m.iconst(lastBranch.statSingletonUse).iload(statUnboxedAllocations)
      m.iconst(0).iconst(0).iconst(0)
      m.iconst(lastBranch.statLabelCreate).invoke(ptw_recordStats)
    }
  }

  private def recordDispatch(loopSave: Int, directTail: Int, singleDispatchTail: Int): Unit = {
    if(config.collectStats) {
      m.aload(ptw).iconst(0).iconst(0).iconst(0).iconst(0).iconst(0).iconst(0)
      m.iconst(loopSave).iconst(directTail).iconst(singleDispatchTail)
      m.iconst(0).invoke(ptw_recordStats)
    }
  }

  private def recordStats(contMarker: VarIdx /* defined if loopSave */, lastBranch: BranchPlan, parents: List[BranchPlan],
    loopCont: Boolean, tailCont: Boolean, singleDispatchTail: Boolean, level: VarIdx): Unit = {
    if(config.collectStats) {
      m.aload(ptw).iconst((lastBranch :: parents).map(_.statSteps).sum)
      m.iload(statCellAllocations).iload(statProxyAllocations).iload(statCachedCellReuse)
      m.iconst(lastBranch.statSingletonUse).iload(statUnboxedAllocations)
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
  }

  private def createCells(instrs: Vector[CreateInstruction]): Unit = {
    val singletonCache = mutable.HashMap.empty[Symbol, VarIdx]
    val allocMetrics = mutable.HashMap.empty[Int, Int]
    instrs.foreach {
      case GetSingletonCell(idx, sym) =>
        assert(!config.unboxedPrimitives)
        cells(idx) = active.find(_.sym == sym) match {
          case Some(a) => a.vidx
          case None =>
            singletonCache.getOrElseUpdate(sym, {
              m.aload(ptw).iconst(symIds(sym)).invoke(ptw_getSingleton).storeLocal(cellT, s"cell${idx}_singleton_${AbstractCodeGen.encodeName(sym)}")
            })
        }
      case ReuseActiveCell(idx, act, sym) =>
        assert(symIds(sym) >= 0)
        assert(!codeGen.shouldUnbox(sym))
        cells(idx) = active(act).vidx
        if(sym != active(act).sym)
          m.lload(active(act).vidx).iconst(mkHeader(symIds(sym))).invokestatic(allocator_putInt)
      case NewCell(_, sym, args) if codeGen.shouldUnbox(sym) =>
        // gets created later
        assert(args.length == 0)
        if(config.collectStats) m.iinc(statUnboxedAllocations)
      case NewCell(idx, sym, args) =>
        val size = cellSize(sym.arity, sym.payloadType)
        m.aload(ptw)
        sym.payloadType match {
          case PayloadType.REF =>
            if(specializedCellAllocSizes.contains(size)) m.invoke(ptw_allocProxiedSpec(size))
            else m.iconst(size).invoke(ptw_allocProxied)
          case _ =>
            if(specializedCellAllocSizes.contains(size)) m.invoke(ptw_allocSpec(size))
            else m.iconst(size).invoke(ptw_allocCell)
        }
        allocMetrics.updateWith(size) { case None => Some(1); case Some(n) => Some(n+1) }
        assert(symIds(sym) >= 0)
        m.dup2.iconst(mkHeader(symIds(sym))).invokestatic(allocator_putInt)
        args.zipWithIndex.foreach {
          case (CellIdx(-1, _), _) => // principal, nothing to connect
          case (_: FreeIdx, _) => // done later when connecting opposite direction
          case (idx, p1) =>
            m.dup2.lconst(auxPtrOffset(p1)).ladd
            ldTaggedCP(idx)
            m.invokestatic(allocator_putLong)
        }
        if(config.collectStats) {
          m.iinc(statCellAllocations)
          if(sym.payloadType == PayloadType.REF) m.iinc(statProxyAllocations)
        }
        cells(idx) = m.storeLocal(cellT, s"cell${idx}_${AbstractCodeGen.encodeName(sym)}")
    }
    allocMetrics.foreach { case (size, count) => incMetric(s"allocCell($size)", m, ptw, count) }
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
  private def loadTempPayload(idx: Int, pt: PayloadType, cls: Class[_]): Unit =
    if(cls == classOf[IntBox] || cls == classOf[LongBox] || cls == classOf[RefBox] ||
      cls == classOf[IntOutput] || cls == classOf[LongOutput] || cls == classOf[RefOutput]) m.aload(temp(idx)._1)
    else {
      val p = PTOps(m, pt)
      if(temp(idx)._2) {
        m.aload(temp(idx)._1)
        p.getBoxValue
      } else p.load(temp(idx)._1)
      if(cls != p.unboxedClass) m.checkcast(tp.o(cls))
    }

  // return VarIdx of unboxed temp var, or None for boxed temp or non-temp arg
  private def unboxedTemp(ea: EmbArg): Option[VarIdx] = ea match {
    case EmbArg.Temp(idx, _) if !temp(idx)._2 => Some(temp(idx)._1)
    case _ => None
  }

  private def loadArg(embArg: EmbArg, cls: Class[_]): () => Unit = {
    val dontFlush = () => ()
    embArg match {
      case EmbArg.Const(i: Int) => m.iconst(i); dontFlush
      case EmbArg.Const(s: String) => m.ldc(s); dontFlush
      case EmbArg.Active(i) => loadCachedPayload(active(i).cachedPayload, cls); dontFlush
      case EmbArg.Temp(idx, pt) => loadTempPayload(idx, pt, cls); dontFlush
      case EmbArg.Cell(idx) =>
        val p = PTOps(m, cellSyms(idx).payloadType)
        val tmp = p.newBoxStoreDup
        () => writeToArg(embArg) { m.aload(tmp); p.getBoxValue }
    }
  }

  private def writeToArg(ea: EmbArg)(loadPayload: => Unit): Unit = ea match {
    case EmbArg.Cell(idx) =>
      val sym = cellSyms(idx)
      active.find(a => a != null && a.reuse == idx) match {
        case Some(ac) if sym.payloadType == PayloadType.REF =>
          m.aload(ac.cachedPayloadProxyPage).iload(ac.cachedPayloadProxyPageOffset).i2l
          loadPayload
          m.invokestatic(allocator_putObject)
        case _ =>
          val p = PTOps(m, sym.payloadType)
          if(codeGen.shouldUnbox(sym)) {
            p.buildUnboxed(symIds(sym)) { loadPayload }
            assert(cells(idx).isEmpty)
            cells(idx) = m.storeLocal(cellT)
          } else p.setCellPayload(ptw, sym.arity) { m.lload(cells(idx)) } { loadPayload }
      }
  }

  private def setLabels(eas: Vector[EmbArg]): Unit = {
    val l = m.storeLocal(tp.J)
    eas.foreach { ea =>
      unboxedTemp(ea) match {
        case Some(vi) => m.lload(l).lstore(vi)
        case None => writeToArg(ea)(m.lload(l))
      }
    }
  }

  private def checkCondition(bp: BranchPlan, endTarget: Label): Unit = {
    bp.cond.foreach {
      case CheckPrincipal(wire: FreeIdx, sym, activeIdx) =>
        if(codeGen.shouldUnbox(sym)) {
          ifUnboxed(wire, sym).not.jump(endTarget)
        } else {
          ifPrincipal(wire).not.jump(endTarget)
          ifBoxed(wire, sym).not.jump(endTarget)
        }
        ldUntaggedCP(wire)
        val acname = AbstractCodeGen.encodeName(sym)
        val vidx = m.storeLocal(cellT, s"ac${activeIdx}_${acname}")
        val ac = new ActiveCell(activeIdx, vidx, sym, sym.arity, bp.needsCachedPayloads(activeIdx), codeGen.shouldUnbox(sym), acname)
        ac.reuse = bp.active(activeIdx)
        active(activeIdx) = ac
        reuseBuffers(activeIdx) = if(ac.reuse == -1) null else new WriteBuffer(ac)
        cachePayload(ac)
      case pc =>
        computePayload(pc, endTarget)
    }
  }

  private def computePayload(pc: PayloadComputationPlan, elseTarget: Label = null): Unit = pc match {
    case AllocateTemp(ea, boxed) =>
      assert(elseTarget == null)
      val name = s"temp${ea.idx}"
      val p = PTOps(m, ea.pt)
      temp(ea.idx) = (if(boxed) p.newBoxStore(name) else m.local(p.desc.unboxedT, name), boxed)
    case CreateLabelsComp(_, ea) =>
      assert(elseTarget == null)
      m.aload(ptw).invoke(ptw_newLabel)
      setLabels(ea)
    case pc: PayloadMethodApplication =>
      if(elseTarget == null) assert(pc.jMethod.getReturnType == Void.TYPE)
      else assert(pc.jMethod.getReturnType == java.lang.Boolean.TYPE)
      callPayloadMethod(m, pc, elseTarget)
    case pc: PayloadAssignment =>
      assert(elseTarget == null)
      assert(pc.payloadType.isDefined)
      val p = PTOps(m, pc.payloadType)
      unboxedTemp(pc.targetIdx) match {
        case Some(vi) =>
          loadArg(pc.sourceIdx, p.unboxedClass)
          p.store(vi)
        case None =>
          writeToArg(pc.targetIdx)(loadArg(pc.sourceIdx, p.unboxedClass))
      }
    case PayloadMethodApplicationWithReturn(method, retIdx) =>
      assert(elseTarget == null)
      unboxedTemp(retIdx) match {
        case Some(vi) =>
          callPayloadMethod(m, method, null)
          PTOps(m, method.embTp.ret.asPT).store(vi)
        case None =>
          writeToArg(retIdx)(callPayloadMethod(m, method, null))
      }
  }

  private def callPayloadMethod(m: MethodDSL, pc: PayloadMethodApplication, elseTarget: Label): Unit = {
    val flush = ArrayBuffer.empty[() => Unit]
    def loadArgs = pc.embArgs.zip(pc.jMethod.getParameterTypes).foreach { case (embArg, cls) => flush += loadArg(embArg, cls) }
    val RuntimeCls = classOf[Runtime.type].getName
    (pc.jMethod.getDeclaringClass.getName, pc.jMethod.getName, pc.embTp.args) match {
      case (RuntimeCls, "eq", Vector((EmbeddedType.PayloadInt, false), (EmbeddedType.PayloadInt, false))) if elseTarget != null =>
        loadArgs
        m.ifI_!=.jump(elseTarget)
      case (RuntimeCls, "eqLabel", _) if elseTarget != null =>
        pc.embArgs.foreach(loadArg(_, classOf[Long]))
        m.lcmp.if_!=.jump(elseTarget)
      case (RuntimeCls, "dupRef", _) =>
        loadArg(pc.embArgs(0), classOf[AnyRef])
        val tmp = m.storeLocal(tp.Object)
        writeToArg(pc.embArgs(1)) { m.aload(tmp) }
        writeToArg(pc.embArgs(2)) {
          m.aload(tmp).dup.instanceof(lifecycleManagedT).if_!=.thn {
            m.checkcast(lifecycleManagedT).invoke(lifecycleManaged_copy)
          }
        }
      case (RuntimeCls, "intAdd", _) =>
        pc.embArgs.foreach(loadArg(_, classOf[Int]))
        m.iadd
      case (RuntimeCls, "intSub", _) =>
        pc.embArgs.foreach(loadArg(_, classOf[Int]))
        m.isub
      case (RuntimeCls, "intMult", _) =>
        pc.embArgs.foreach(loadArg(_, classOf[Int]))
        m.imul
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
        flush.foreach(_())
        if(elseTarget != null) m.ifeq(elseTarget)
    }
  }
}
