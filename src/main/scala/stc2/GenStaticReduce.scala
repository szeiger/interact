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
  val cells = new Array[Cell](rule.totalCellCount)
  // cell reuse buffers, updated for the current top-level branch
  val reuseBuffers: Array[WriteBuffer] = new Array(rule.totalActiveCount)
  // payload temp vars and boxed flag, updated for the current branches
  val temp = new Array[(VarIdx, Boolean)](rule.totalTempCount)

  // cached payloads, updated for the current top-level branch
  for(ac <- active if ac != null) cachePayload(ac)
  private def cachePayload(ac: ActiveCell): Unit = {
    if(ac.needsCachedPayload && ac.vidx.isDefined) {
      val name = s"ac${ac.id}u_${ac.encName}"
      ac.sym.payloadType match {
        case PayloadType.REF =>
          m.aload(ptw).lload(ac.vidx).invoke(ptw_getProxyPage)
          ac.cachedPayloadProxyPage = m.dup.storeLocal(tp.Object, s"${name}PP")
          m.lload(ac.vidx).lconst(Allocator.proxyElemOffset).ladd.invokestatic(allocator_getInt)
          ac.cachedPayloadProxyPageOffset = m.dup.storeLocal(tp.I, s"${name}PPOff")
          ac.cachedPayload = m.i2l.invokestatic(allocator_getObject).storeLocal(tp.Object, name)
        case pt =>
          val p = PTOps(m, pt)
          if(ac.unboxed) p.untag { m.lload(ac.vidx) }
          else p.getCellPayload(ptw, ac.arity) { m.lload(ac.vidx) }
          ac.cachedPayload = m.storeLocal(p.unboxedT, name)
      }
    }
  }

  class Cell(idx: Int, val sym: Symbol) {
    private[this] lazy val pt = PTOps(m, sym.payloadType)
    var tagged, untagged = VarIdx.none
    def isTagged = tagged.isDefined
    def hasUntaggedValue = untagged.isDefined
    def ldTagged: Unit = {
      if(hasUntaggedValue) pt.tag(symIds(sym))(pt.load(untagged))
      else m.lload(tagged)
    }
    def ldUntagged: Unit = {
      if(hasUntaggedValue) pt.load(untagged)
      else pt.untag(m.lload(tagged))
    }
    def storeTagged: Unit = tagged = m.storeLocal(cellT, s"cell${idx}_${AbstractCodeGen.encodeName(sym)}")
    def storeUntagged: Unit = untagged = m.storeLocal(pt.unboxedT, s"cell${idx}u_${AbstractCodeGen.encodeName(sym)}")
  }

  private def symbolOf(idx: Idx) = idx match {
    case CellIdx(i, -1) => cells(i).sym
    case _ => Symbol.NoSymbol
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
        cells(cellIdx).ldTagged
        m.lconst(auxPtrOffset(p)).ladd
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
        val c = cells(idx.idx)
        if(c.isTagged || c.hasUntaggedValue) {
          c.ldTagged
          var l = auxPtrOffset(idx.port)
          if(idx.port >= 0) l += TAG_AUX_PTR
          if(l != 0) {
            m.lconst(l).ladd
            None
          } else if(c.hasUntaggedValue) None
          else Some(c.tagged)
        } else {
          assert(shouldUnbox(c.sym) && idx.port == -1)
          if(c.sym.payloadType == PayloadType.VOID) m.lconst(mkUnboxed(symIds(c.sym)).toLong & 0xffffffffL)
          else {
            val ac = active.find(a => a != null && a.reuse == idx.idx).get
            if(ac.unboxedParameter) ac.pt.tag(symIds(ac.sym)) { ac.pt.load(ac.cachedPayload) }
            else m.lload(ac.vidx)
          }
          None
        }
    }
  }

  private def ldUntaggedPayload(idx: CellIdx): Unit = {
    val c = cells(idx.idx)
    assert(idx.port == -1&& shouldUnbox(c.sym), s"idx.port=${idx.port}, isTagged=${c.isTagged}, shouldUnbox=${shouldUnbox(c.sym)}")
    if(c.isTagged || c.hasUntaggedValue) c.ldUntagged
    else if(c.sym.payloadType != PayloadType.VOID) {
      val ac = active.find(a => a != null && a.reuse == idx.idx).get
      assert(ac.unboxedParameter)
      ac.pt.load(ac.cachedPayload)
    }
  }

  private def ldCPAddress(idx: Idx): Option[VarIdx] = {
    idx match {
      case idx: FreeIdx =>
        ldTaggedCP(idx)
        m.lconst(ADDRMASK).land
        None
      case idx: CellIdx =>
        if(!cells(idx.idx).isTagged) {
          ldTaggedCP(idx)
        } else {
          cells(idx.idx).ldTagged
          auxPtrOffset(idx.port) match {
            case 0 => Some(cells(idx.idx).tagged)
            case off => m.lconst(off).ladd; None
          }
        }
    }
  }

  // Write to internal cell or reuse buffer for reused cells
  private def setAux(idx: CellIdx, ct2: Idx): Unit =
    reuseBuffers.find(w => w != null && w.cellIdx == idx.idx) match {
      case Some(b) => b.set(idx.port, ct2)
      case None =>
        cells(idx.idx).ldTagged
        m.lconst(auxPtrOffset(idx.port)).ladd
        ldTaggedCP(ct2)
        m.invokestatic(allocator_putLong)
    }

  private[this] def ifBoxed(idx: FreeIdx, sym: Symbol): ThenDSL = {
    // must have already checked ifPrincipal if config.unboxedPrimitives is enabled!
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
    m.l2i.iconst(TAGMASK.toInt).iand.iconst(TAG_AUX_PTR).ifI_==
  }

  private[this] def ifPrincipal(idx: FreeIdx): ThenDSL = {
    ldTaggedCP(idx)
    m.l2i.iconst(TAGMASK.toInt).iand.if_==
  }

  // Boxed, unboxed or untagged continuation half-pair
  class Cont(idx: Int, knownSym: Symbol, unconditional: Boolean) {
    private[this] val untaggedPT = if(knownSym.isDefined && shouldUnbox(knownSym)) Some(PTOps(m, knownSym.payloadType)) else None
    private[this] val options = mutable.HashSet.empty[VarIdx]
    private[this] var (tagged, untagged, varName) = untaggedPT match {
      case Some(pt) if pt.isVoid => (VarIdx.none, VarIdx.none, null)
      case Some(pt) =>
        val n = s"cont${idx}_${pt.unboxedT.jvmClass.get.getName}"
        if(unconditional) (VarIdx.none, VarIdx.none, n)
        else {
          val v = m.local(pt.unboxedT, n)
          pt.loadConst0.store(v)
          (VarIdx.none, v, null)
        }
      case None =>
        val n = s"cont$idx"
        if(unconditional) (VarIdx.none, VarIdx.none, n)
        else {
          val v = m.local(cellT, n)
          m.lconst(0).lstore(v)
          (v, VarIdx.none, null)
        }
    }

    def isTagged = tagged.isDefined

    def set(ct: Idx): Unit = untaggedPT match {
      case Some(pt) if pt.isVoid => options += VarIdx.none
      case Some(pt) =>
        if(unconditional) {
          assert(untagged.isEmpty)
          untagged = m.local(pt.unboxedT, varName)
        }
        ldUntaggedPayload(ct.asInstanceOf[CellIdx])
        pt.store(untagged)
      case None =>
        if(unconditional) {
          assert(tagged.isEmpty)
          tagged = m.local(cellT, varName)
        }
        options += ldTaggedCP(ct).getOrElse(VarIdx.none)
        m.lstore(tagged)
    }
    def maybeSet = options.nonEmpty

    def storeIn(ac: ActiveCell): Unit = untaggedPT match {
      case Some(pt) if pt.isVoid =>
      case Some(pt) =>
        assert(ac.unboxedParameter, s"$baseMetricName, $knownSym, $ac, ${pt.unboxedT.desc}")
        assert(knownSym == ac.sym)
        if(options != mutable.Set(ac.cachedPayload) && !ac.unboxedVoid) {
          pt.load(untagged)
          ac.pt.store(ac.cachedPayload)
        }
      case None =>
        if(ac.unboxedParameter) {
          if(options != mutable.Set(ac.cachedPayload) && !ac.unboxedVoid) {
            ac.pt.untag { m.lload(tagged) }
            ac.pt.store(ac.cachedPayload)
          }
        } else {
          if(options != mutable.Set(ac.vidx))
            m.lload(tagged).lstore(ac.vidx)
        }
    }

    // load tagged or untagged, suitable for a static reduce call
    def ldAsParam: Unit = untaggedPT match {
      case Some(pt) if pt.isVoid =>
      case Some(pt) =>
        pt.load(untagged)
      case None =>
        m.lload(tagged)
    }

    def ldTagged: Unit = untaggedPT match {
      case Some(pt) if pt.isVoid => m.lconst(mkUnboxed(symIds(knownSym)).toLong & 0xffffffffL)
      case Some(pt) => pt.tag(symIds(knownSym)) { pt.load(untagged) }
      case None => m.lload(tagged)
    }
  }

  def ldAndSetAux(ct1: FreeIdx, ct2: Idx) = {
    ldCPAddress(ct1)
    ldTaggedCP(ct2)
    m.invokestatic(allocator_putLong)
  }

  def addActive(ct1: Idx, ct2: Idx) = {
    m.aload(ptw)
    ldTaggedCP(ct1)
    ldTaggedCP(ct2)
    m.invoke(ptw_addActive)
  }

  def emitBranches(bps: Vector[BranchPlan], parents: List[BranchPlan], branchMetricName: String): Unit = {
    bps.zipWithIndex.foreach { case (bp, branchIdx) =>
      val branchEnd = m.newLabel
      bp.cond.foreach(computePayload(_, branchEnd))
      emitBranch(bp, parents, s"$branchMetricName#$branchIdx")
      if(bp.cond.isDefined) m.setLabel(branchEnd)
    }
  }

  def emitBranch(bp: BranchPlan, parents: List[BranchPlan], branchMetricName: String): Unit = {
    if(parents.isEmpty) {
      active(0).reuse = bp.active(0)
      active(1).reuse = bp.active(1)
      for(i <- 2 until active.length) active(i) = null
      for(i <- active.indices)
        reuseBuffers(i) = if(active(i) == null || active(i).reuse == -1) null else new WriteBuffer(active(i))
    }

    for(i <- bp.cellOffset until cells.length)
      cells(i) = if(i-bp.cellOffset < bp.cellSyms.length) new Cell(i, bp.cellSyms(i-bp.cellOffset)) else null

    incMetric(s"$branchMetricName", m, ptw)
    val useLoopCont = bp.useLoopCont && bp.unconditionalTail.isEmpty

    val cont = bp.unconditionalTail match {
      case Some((s1, s2)) => Vector(new Cont(0, s1, true), new Cont(1, s2, true))
      case _ if useLoopCont => Vector(new Cont(0, rule.sym1, false), new Cont(1, rule.sym2, false))
      case _ if bp.useTailCont => Vector(new Cont(0, bp.singleDispatchSym0, false), new Cont(1, bp.singleDispatchSym1, false))
      case _ => null
    }
    def setCont(ct1: Idx, ct2: Idx): Unit = { cont(0).set(ct1); cont(1).set(ct2) }
    def ifContSet = {
      if(cont(0).isTagged) cont(0).ldTagged
      else {
        assert(cont(1).isTagged)
        cont(1).ldTagged
      }
      m.lconst(0).lcmp.if_!=
    }

    createCells(bp.instructions, bp)

    bp.payloadComps.foreach(computePayload(_))

    def connectActivePairLoop(ct1: CellIdx, ct2: FreeIdx): Unit = {
      val mayLoopOn0 = ct1.idx == bp.active(0) && bp.loopOn0
      val mayLoopOn1 = ct1.idx == bp.active(1) && bp.loopOn1
      if(mayLoopOn0 || mayLoopOn1) {
        val (sym, ctA, ctB) = if(mayLoopOn0) (active(1).sym, ct1, ct2) else (active(0).sym, ct2, ct1)
        val lCreateCut, lEnd = m.newLabel
        if(cont(0).maybeSet) ifContSet.jump(lCreateCut)
        if(shouldUnbox(sym))
          ifUnboxed(ct2, sym).not.jump(lCreateCut)
        else {
          if(config.unboxedPrimitives) ifPrincipal(ct2).not.jump(lCreateCut)
          ifBoxed(ct2, sym).not.jump(lCreateCut)
        }
        setCont(ctA, ctB)
        m.goto(lEnd)
        m.setLabel(lCreateCut)
        addActive(ct1, ct2)
        m.setLabel(lEnd)
      } else {
        connectActivePair(ct1, ct2)
      }
    }

    def connectActivePair(ct1: CellIdx, ct2: Idx): Unit = {
      if(bp.useTailCont && !useLoopCont) {
        bp.unconditionalTail match {
          case Some((s1, s2)) =>
            val cts = (symbolOf(ct1), symbolOf(ct2))
            if((cts == (s1, s2) || cts == (s2, s1)) && !cont(0).maybeSet) {
              if(cts == (s1, s2)) setCont(ct1, ct2) else setCont(ct2, ct1)
            } else addActive(ct1, ct2)
          case None =>
            if(!cont(0).maybeSet) setCont(ct1, ct2)
            else ifContSet.thnElse { addActive(ct1, ct2) } { setCont(ct1, ct2) }
        }
      } else addActive(ct1, ct2)
    }

    // Connect remaining wires
    def connectCF(ct1: CellIdx, ct2: FreeIdx): Unit = cachedIdx(ct2) {
      if(ct1.isAux) {
        setAux(ct1, ct2)
        ifAux(ct2).thn { ldAndSetAux(ct2, ct1) }
      } else {
        ifAux(ct2).thnElse { ldAndSetAux(ct2, ct1) } { connectActivePairLoop(ct1, ct2) }
      }
    }
    def connectFF(ct1: FreeIdx, ct2: FreeIdx): Unit = cachedIdx(ct1, ct2) {
      ifAux(ct1).thnElse {
        ldAndSetAux(ct1, ct2)
        ifAux(ct2).thn { ldAndSetAux(ct2, ct1) }
      } {
        ifAux(ct2).thnElse { ldAndSetAux(ct2, ct1) } { addActive(ct1, ct2) }
      }
    }
    def connectCC(ct1: CellIdx, ct2: CellIdx): Unit = {
      if(ct1.isAux && !bp.cellPortsConnected.contains(ct1))
        setAux(ct1, ct2)
      if(ct2.isAux && !bp.cellPortsConnected.contains(ct2))
        setAux(ct2, ct1)
      if(ct1.isPrincipal && ct2.isPrincipal)
        connectActivePair(ct1, ct2)
    }
    bp.sortedConns.foreach {
      case Connection(i1: FreeIdx, i2: FreeIdx) => connectFF(i1, i2)
      case Connection(i1: CellIdx, i2: FreeIdx) => connectCF(i1, i2)
      case Connection(i1: CellIdx, i2: CellIdx) => connectCC(i1, i2)
    }

    if(bp.branches.nonEmpty)
      emitBranches(bp.branches, bp :: parents, branchMetricName)
    else {
      for(w <- reuseBuffers if w != null) w.flush()
      for(ac <- active if ac != null && ac.reuse == -1 && (!ac.sym.isDefined || !ac.sym.isSingleton) && !ac.unboxed) {
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

      recordSteps(bp, parents)

      if(useLoopCont) {
        ifContSet.thn {
          recordDispatch(1, 0, 0)
          cont(0).storeIn(active(0))
          cont(1).storeIn(active(1))
          m.goto(methodStart) //TODO jump directly to the right branch if it can be determined statically
        }
      } else if(bp.useTailCont) {
        bp.unconditionalTail match {
          case Some((cont0Sym, cont1Sym)) =>
            if(cont0Sym == active(0).sym && cont1Sym == active(1).sym) {
              recordDispatch(1, 0, 0)
              cont(0).storeIn(active(0))
              cont(1).storeIn(active(1))
              m.goto(methodStart)
            } else {
              staticReduceFor(cont0Sym, cont1Sym) match {
                case Some((mref, rev)) =>
                  m.iload(level).if_!=.thnElse {
                    m.iinc(level, -1)
                    recordDispatch(0, 1, 1)
                    if(rev) { cont(1).ldAsParam; cont(0).ldAsParam } else { cont(0).ldAsParam; cont(1).ldAsParam }
                    m.iload(level).aload(ptw)
                    m.invokestatic(mref)
                  } {
                    m.aload(ptw)
                    cont(0).ldTagged
                    cont(1).ldTagged
                    m.invoke(ptw_addActive)
                  }
                case None =>
                  m.aload(ptw)
                  cont(0).ldTagged
                  cont(1).ldTagged
                  m.invoke(ptw_addIrreducible)
              }
            }
          case None =>
            ifContSet.thn {
              m.iload(level).if_!=.thnElse {
                m.iinc(level, -1)
                if(bp.singleDispatchSym0.isDefined) {
                  recordDispatch(0, 1, 1)
                  cont(0).ldAsParam
                  cont(1).ldTagged
                  m.iload(level).aload(ptw)
                  m.invokestatic(metaClass_reduce(bp.singleDispatchSym0))
                } else {
                  recordDispatch(0, 1, 0)
                  cont(0).ldTagged
                  cont(1).ldTagged
                  m.iload(level).aload(ptw)
                  m.invokestatic(generatedDispatch_staticReduce)
                }
              } {
                m.aload(ptw)
                cont(0).ldTagged
                cont(1).ldTagged
                m.invoke(ptw_addActive)
              }
            }
        }
      }

      m.return_
    }
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

  def emitRule(): Unit = {
    emitBranches(rule.branches, Nil, baseMetricName)
  }

  private def createCells(instrs: Vector[Instruction], bp: BranchPlan): Unit = {
    val singletonCache = mutable.HashMap.empty[Symbol, VarIdx]
    val allocMetrics = mutable.HashMap.empty[Int, Int]
    instrs.foreach {
      case ActivateCell(wire, sym, activeIdx) =>
        ldTaggedCP(wire)
        val acname = AbstractCodeGen.encodeName(sym)
        val vidx = m.storeLocal(cellT, s"ac${activeIdx}_${acname}")
        val ac = new ActiveCell(m, codeGen, activeIdx, vidx, sym, sym.arity, bp.needsCachedPayloads(activeIdx), codeGen.shouldUnbox(sym), acname)
        ac.reuse = bp.active(activeIdx)
        active(activeIdx) = ac
        reuseBuffers(activeIdx) = if(ac.reuse == -1) null else new WriteBuffer(ac)
        cachePayload(ac)
      case GetSingletonCell(idx, sym) =>
        assert(!config.unboxedPrimitives)
        cells(idx).tagged = active.find(_.sym == sym) match {
          case Some(a) => a.vidx
          case None =>
            singletonCache.getOrElseUpdate(sym, {
              m.aload(ptw).iconst(symIds(sym)).invoke(ptw_getSingleton).storeLocal(cellT, s"cell${idx}_singleton_${AbstractCodeGen.encodeName(sym)}")
            })
        }
      case ReuseActiveCell(idx, act, sym) =>
        assert(symIds(sym) >= 0)
        assert(!codeGen.shouldUnbox(sym))
        cells(idx).tagged = active(act).vidx
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
        cells(idx).storeTagged
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
        val p = PTOps(m, cells(idx).sym.payloadType)
        val tmp = p.newBoxStoreDup
        () => writeToArg(embArg) { m.aload(tmp); p.getBoxValue }
    }
  }

  private def writeToArg(ea: EmbArg)(loadPayload: => Unit): Unit = ea match {
    case EmbArg.Cell(idx) =>
      val sym = cells(idx).sym
      active.find(a => a != null && a.reuse == idx) match {
        case Some(ac) if sym.payloadType == PayloadType.REF =>
          m.aload(ac.cachedPayloadProxyPage).iload(ac.cachedPayloadProxyPageOffset).i2l
          loadPayload
          m.invokestatic(allocator_putObject)
        case _ =>
          val p = PTOps(m, sym.payloadType)
          if(codeGen.shouldUnbox(sym)) {
            assert(!cells(idx).isTagged && !cells(idx).hasUntaggedValue)
            loadPayload
            cells(idx).storeUntagged
          } else p.setCellPayload(ptw, sym.arity) { cells(idx).ldTagged } { loadPayload }
      }
  }

  private def computePayload(pc: PayloadComputationPlan, elseTarget: Label = null): Unit = pc match {
    case CheckPrincipal(wire: FreeIdx, sym, _) =>
      if(codeGen.shouldUnbox(sym)) {
        ifUnboxed(wire, sym).not.jump(elseTarget)
      } else {
        ifPrincipal(wire).not.jump(elseTarget)
        ifBoxed(wire, sym).not.jump(elseTarget)
      }
    case AllocateTemp(ea, boxed) =>
      assert(elseTarget == null)
      val name = s"temp${ea.idx}"
      val p = PTOps(m, ea.pt)
      temp(ea.idx) = (if(boxed) p.newBoxStore(name) else m.local(p.unboxedT, name), boxed)
    case CreateLabelsComp(_, eas) =>
      assert(elseTarget == null)
      val l = m.aload(ptw).invoke(ptw_newLabel).storeLocal(tp.J)
      eas.foreach { ea =>
        unboxedTemp(ea) match {
          case Some(vi) => m.lload(l).lstore(vi)
          case None => writeToArg(ea)(m.lload(l))
        }
      }
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
