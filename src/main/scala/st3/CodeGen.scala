package de.szeiger.interact.st3

import de.szeiger.interact.codegen.AbstractCodeGen
import de.szeiger.interact.{CellIdx, Connection, FreeIdx, GenericRuleImpl, Idx, Symbol}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

import scala.collection.mutable

class CodeGen(genPackage: String, logGenerated: Boolean) extends AbstractCodeGen[RuleImpl]("de/szeiger/interact/st3", genPackage, logGenerated) {
  private val MAX_SPEC_CELL = 2
  private val ptwT = tp.c(s"$interpreterPackage/PerThreadWorker")
  private val cellT = tp.c(s"$interpreterPackage/Cell")
  private val cellNT = tp.c(s"$interpreterPackage/CellN")
  private val cellSpecTs = (0 to MAX_SPEC_CELL).map(i => tp.c(s"$interpreterPackage/Cell$i"))
  private val cell_symId = cellT.method("symId", tp.m().I)
  private val cell_symIdSetter = cellT.method("symId_$eq", tp.m(tp.I).V)
  private val cell_auxCell = cellT.method("auxCell", tp.m(tp.I)(cellT))
  private val cell_auxPort = cellT.method("auxPort", tp.m(tp.I)(tp.I))
  private val cell_setAux = cellT.method("setAux", tp.m(tp.I, cellT, tp.I).V)
  private val cell_setCell = cellT.method("setCell", tp.m(tp.I, cellT, tp.I).V)
  private val cell_pcell = cellT.method("pcell", tp.m()(cellT))
  private val cell_pport = cellT.method("pport", tp.m()(tp.I))
  private val cell_pcellSetter = cellT.method("pcell_$eq", tp.m(cellT).V)
  private val cell_pportSetter = cellT.method("pport_$eq", tp.m(tp.I).V)
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
  private val ptw_createCut = ptwT.method("createCut", tp.m(cellT).V)
  private val new_CellN_II = cellNT.constr(tp.m(tp.I, tp.I).V)
  private val new_CellSpec = cellSpecTs.zipWithIndex.map { case (t, a) =>
    val params = Seq(tp.I) ++ (0 to a).flatMap(_ => Seq(cellT, tp.I))
    t.constr(tp.m(params: _*).V)
  }

  protected def implementRuleClass(c: ClassDSL, sids: Map[Symbol, Int], sidFields: IndexedSeq[FieldRef], g: GenericRuleImpl): Unit = {
    val allConns = g.wireConnsDistinct ++ g.internalConns
    var cellAllocations = 0

    // If cell(cellIdx) replaces rhs/lhs, how many connections stay the same?
    def countReuseConnections(cellIdx: Int, rhs: Boolean): Int =
      reuseSkip(cellIdx, rhs).length
    // Find connections to skip for reuse
    def reuseSkip(cellIdx: Int, rhs: Boolean): IndexedSeq[Connection] =
      (0 until g.cells(cellIdx).arity).flatMap { p =>
        val ci = new CellIdx(cellIdx, p)
        g.wireConnsDistinct.collect {
          case c @ Connection(FreeIdx(rhs2, fi2), ci2) if ci2 == ci && rhs2 == rhs && fi2 == p => c
          case c @ Connection(ci2, FreeIdx(rhs2, fi2)) if ci2 == ci && rhs2 == rhs && fi2 == p => c
        }
      }
    // Find cellIdx/sym/quality of best reuse candidate for rhs/lhs
    // - Prefer max. reuse first, then same symbol
    def bestReuse(candidates: Array[(Symbol, Int)], rhs: Boolean): Option[(Symbol, Int, Int)] =
      candidates.map { case (s, i) => (s, i, 2*countReuseConnections(i, rhs) + (if(s == g.symFor(rhs)) 1 else 0)) }
        .sortBy { case (s, i, q) => -q }.headOption
    // Find sym/cellIdx of cells with same arity as rhs/lhs
    def reuseCandidates(rhs: Boolean): Array[(Symbol, Int)] =
      g.cells.zipWithIndex.filter { case (sym, _) => sym.arity == g.symFor(rhs).arity }
    // Find best reuse combination for both sides
    def bestReuse2: (Option[(Symbol, Int, Int)], Option[(Symbol, Int, Int)], Set[Connection]) = {
      var cand1 = reuseCandidates(false)
      var cand2 = reuseCandidates(true)
      var best1 = bestReuse(cand1, false)
      var best2 = bestReuse(cand2, true)
      (best1, best2) match {
        case (Some((s1, ci1, q1)), Some((si2, ci2, q2))) if ci1 == ci2 =>
          if(q1 >= q2) { // redo best2
            cand2 = cand2.filter { case (s, i) => i != ci1 }
            best2 = bestReuse(cand2, true)
          } else { // redo best1
            cand1 = cand1.filter { case (s, i) => i != ci2 }
            best1 = bestReuse(cand1, false)
          }
        case _ =>
      }
      val skipConn1 = best1.iterator.flatMap { case (_, ci, _) => reuseSkip(ci, false) }
      val skipConn2 = best2.iterator.flatMap { case (_, ci, _) => reuseSkip(ci, true) }
      (best1, best2, (skipConn1 ++ skipConn2).toSet)
    }

    val (reuse1, reuse2, skipConns) = {
      val (r1, r2, skip) = bestReuse2
      (r1.map(_._2).getOrElse(-1), r2.map(_._2).getOrElse(-1), skip)
    }
    def isReuse(cellIdx: Int): Boolean = cellIdx == reuse1 || cellIdx == reuse2

    val m = c.method(Acc.PUBLIC, "reduce", tp.m(cellT, ptwT).V)
    val cut1 = m.param("cut1", cellT, Acc.FINAL)
    val ptw = m.param("ptw", ptwT, Acc.FINAL)

    def getCell(a: Int, p: Int): m.type = {
      if(p < 0) m.invokevirtual(cell_pcell)
      else if(a < cell_acell.length) m.invokevirtual(cell_acell(a)(p))
      else m.iconst(p).invokevirtual(cell_auxCell)
    }
    def getPort(a: Int, p: Int): m.type = {
      if(p < 0) m.invokevirtual(cell_pport)
      else if(a < cell_aport.length) m.invokevirtual(cell_aport(a)(p))
      else m.iconst(p).invokevirtual(cell_auxPort)
    }
    def setCell(a: Int, p: Int, skipPort: Boolean = false)(loadC2: => Unit)(loadP2: => Unit): m.type = {
      if(p < 0) {
        if(!skipPort) {
          m.dup
          loadP2; m.invokevirtual(cell_pportSetter)
        }
        loadC2; m.invokevirtual(cell_pcellSetter)
      } else if(a < cell_acell.length) {
        if(!skipPort) {
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
    def storeCastCell(name: String, arity: Int, start: Label = null): VarIdx = {
      if(arity < cellSpecTs.length) m.checkcast(cellSpecTs(arity))
      val v = m.storeLocal(name, cellT, Acc.FINAL, start = start)
      v
    }

    val cut2 = m.aload(cut1).invokevirtual(cell_pcell).storeLocal("cut2", cellT, Acc.FINAL)
    m.aload(cut1).invokevirtual(cell_symId)
    m.aload(m.receiver).getfield(sidFields(0))
    m.ifThenElseI_== { m.aload(cut1).aload(cut2) } { m.aload(cut2).aload(cut1) }
    val l1 = m.newLabel
    val cRight = storeCastCell("cRight", g.arity2, start = l1)
    val cLeft = storeCastCell("cLeft", g.arity1, start = l1)
    m.label(l1)

    val lhs = (0 until g.arity1).map { idx =>
      m.aload(cLeft).dup
      val c = getCell(g.arity1, idx).storeLocal(s"lhsc$idx", cellT, Acc.FINAL)
      val p = getPort(g.arity1, idx).storeLocal(s"lhsp$idx", tp.I, Acc.FINAL)
      (c, p)
    }
    val rhs = (0 until g.arity2).map { idx =>
      m.aload(cRight).dup
      val c = getCell(g.arity2, idx).storeLocal(s"rhsc$idx", cellT, Acc.FINAL)
      val p = getPort(g.arity2, idx).storeLocal(s"rhsp$idx", tp.I, Acc.FINAL)
      (c, p)
    }

    val cells: mutable.ArraySeq[VarIdx] = {
      val cells = mutable.ArraySeq.fill[VarIdx](g.cells.length)(VarIdx.none)
      def createCell(sym: Symbol, cellIdx: Int): m.type = {
        if(sym.arity < new_CellSpec.length) {
          m.newInitDup(new_CellSpec(sym.arity)) {
            m.aload(m.receiver).getfield(sidFields(sids(sym)))
            g.cellConns(cellIdx).map {
              case CellIdx(ci, p) =>
                if(cells(ci) == VarIdx.none) m.aconst_null else m.aload(cells(ci))
                m.iconst(p)
              case FreeIdx(r, idx) =>
                val (c2, p2) = if(r) rhs(idx) else lhs(idx)
                m.aload(c2).iload(p2)
            }
          }
        } else {
          m.newInitDup(new_CellN_II) {
            m.aload(m.receiver).getfield(sidFields(sids(sym)))
            m.iconst(sym.arity)
          }
        }
      }
      def updateSym(cell: VarIdx, sym: Symbol): Unit =
        m.aload(cell).aload(m.receiver).getfield(sidFields(sids(sym))).invokevirtual(cell_symIdSetter)
      for(idx <- cells.indices) {
        cells(idx) = g.cells(idx) match {
          case sym if idx == reuse1 =>
            if(sym != g.sym1) updateSym(cLeft, sym)
            cLeft
          case sym if idx == reuse2 =>
            if(sym != g.sym2) updateSym(cRight, sym)
            cRight
          case sym =>
            cellAllocations += 1
            createCell(sym, idx).storeLocal(s"c$idx", cellT, Acc.FINAL)
        }
      }
      cells
    }

    def connectCF(ct1: CellIdx, ct2: FreeIdx): Unit = {
      val (c1, p1) = (ct1.idx, ct1.port)
      val (c2, p2) = if(ct2.rhs) rhs(ct2.idx) else lhs(ct2.idx)
      if(isReuse(c1)) {
        m.aload(cells(c1))
        setCell(g.cells(c1).arity, p1)(m.aload(c2))(m.iload(p2))
      }
      m.aload(c2).iload(p2).aload(cells(c1)).iconst(p1).invokevirtual(cell_setCell)
      if(p1 < 0)
        m.iload(p2).iconst(0).ifThenI_< { m.aload(ptw).aload(cells(c1)).invokevirtual(ptw_createCut) }
    }
    def connectFF(ct1: FreeIdx, ct2: FreeIdx): Unit = {
      val (c1, p1) = if(ct1.rhs) rhs(ct1.idx) else lhs(ct1.idx)
      val (c2, p2) = if(ct2.rhs) rhs(ct2.idx) else lhs(ct2.idx)
      m.aload(c1).iload(p1).aload(c2).iload(p2).invokevirtual(cell_setCell)
      m.aload(c2).iload(p2).aload(c1).iload(p1).invokevirtual(cell_setCell)
      m.iload(p1).iload(p2).iand.iconst(0).ifThenI_< { m.aload(ptw).aload(c1).invokevirtual(ptw_createCut) }
    }
    def connectCC(ct1: CellIdx, ct2: CellIdx): Unit = {
      val (c1, p1) = (ct1.idx, ct1.port)
      val (c2, p2) = (ct2.idx, ct2.port)
      if(c2 >= c1 || isReuse(c1)) {
        m.aload(cells(c1))
        setCell(g.cells(c1).arity, p1, !isReuse(c1))(m.aload(cells(c2)))(m.iconst(p2))
      }
      if(c1 >= c2 || isReuse(c2)) {
        m.aload(cells(c2))
        setCell(g.cells(c2).arity, p2, !isReuse(c2))(m.aload(cells(c1)))(m.iconst(p1))
      }
      if(p1 < 0 && p2 < 0) m.aload(ptw).aload(cells(c1)).invokevirtual(ptw_createCut)
    }
    allConns.foreach {
      case c if skipConns.contains(c) => ()
      case Connection(i1: FreeIdx, i2: FreeIdx) => connectFF(i1, i2)
      case Connection(i1: FreeIdx, i2: CellIdx) => connectCF(i2, i1)
      case Connection(i1: CellIdx, i2: FreeIdx) => connectCF(i1, i2)
      case Connection(i1: CellIdx, i2: CellIdx) => connectCC(i1, i2)
    }
    m.return_

    // statistics
    c.method(Acc.PUBLIC, "cellAllocationCount", tp.m().I).iconst(cellAllocations).ireturn
  }
}
