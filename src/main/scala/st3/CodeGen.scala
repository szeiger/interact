package de.szeiger.interact.st3

import de.szeiger.interact.codegen.AbstractCodeGen
import de.szeiger.interact.{CellIdx, Connection, FreeIdx, GenericRuleImpl, Symbol}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

class CodeGen(genPackage: String) extends AbstractCodeGen[RuleImpl]("de/szeiger/interact/st3", genPackage) {
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
  private val new_CellSpec_I = cellSpecTs.map(_.constr(tp.m(tp.I).V))

  protected def implementRuleClass(c: ClassDSL, sids: Map[Symbol, Int], sidFields: IndexedSeq[FieldRef], g: GenericRuleImpl): Unit = {
    val internalConns = g.internalConns.toArray
    val allConns = (g.wireConnsDistinct ++ internalConns.iterator).toArray
    var cellAllocations = 0

    val (reuse1, reuse2) = {
      // Find individual cells for reuse (with potential relabeling)
      val sameA = g.sym1.arity == g.sym2.arity
      var matchingArity1 = g.cells.zipWithIndex.filter { case (sym, _) => sym.arity == g.sym1.arity }
      var matchingArity2 = g.cells.zipWithIndex.filter { case (sym, _) => sym.arity == g.sym2.arity }
      // Find full Symbol matches first
      var match1 = matchingArity1.find { case (sym, _) => sym == g.sym1 }.orNull
      if(match1 != null && sameA) matchingArity2 = matchingArity2.filter(_._2 != match1._2)
      var match2 = matchingArity2.find { case (sym, _) => sym == g.sym2 }.orNull
      if(match2 != null && sameA) matchingArity1 = matchingArity1.filter(_._2 != match2._2)
      // Find arity matches
      if(match1 == null) {
        match1 = matchingArity1.headOption.orNull
        if(match1 != null && sameA) matchingArity2 = matchingArity2.filter(_._2 != match1._2)
      }
      if(match2 == null) match2 = matchingArity2.headOption.orNull
      (if(match1 != null) match1._2 else -1, if(match2 != null) match2._2 else -1)
    }

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
    def setCell(a: Int, p: Int)(loadC2: => Unit)(loadP2: => Unit): m.type = {
      if(p < 0) {
        m.dup
        loadC2; m.invokevirtual(cell_pcellSetter)
        loadP2; m.invokevirtual(cell_pportSetter)
      } else if(a < cell_acell.length) {
        m.dup
        loadC2; m.invokevirtual(cell_acellSetter(a)(p))
        loadP2; m.invokevirtual(cell_aportSetter(a)(p))
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

    def updateSym(cell: VarIdx, sym: Symbol): Unit =
      m.aload(cell).aload(m.receiver).getfield(sidFields(sids(sym))).invokevirtual(cell_symIdSetter)
    val cells = g.cells.zipWithIndex.map {
      case (sym, idx) if idx == reuse1 =>
        if(sym != g.sym1) updateSym(cLeft, sym)
        cLeft
      case (sym, idx) if idx == reuse2 =>
        if(sym != g.sym2) updateSym(cRight, sym)
        cRight
      case (sym, idx) =>
        cellAllocations += 1
        if(sym.arity < new_CellSpec_I.length) {
          m.newInitDup(new_CellSpec_I(sym.arity)) {
            m.aload(m.receiver).getfield(sidFields(sids(sym)))
          }
        } else {
          m.newInitDup(new_CellN_II) {
            m.aload(m.receiver).getfield(sidFields(sids(sym)))
            m.iconst(sym.arity)
          }
        }
        m.storeLocal(s"c$idx", cellT, Acc.FINAL)
    }

    allConns.foreach { case conn @ Connection(idx1, idx2) =>
      def connectCF(ct1: CellIdx, ct2: FreeIdx): Unit = {
        val (c1, p1) = (ct1.idx, ct1.port)
        val (c2, p2) = if(ct2.rhs) rhs(ct2.idx) else lhs(ct2.idx)
        m.aload(cells(c1)); setCell(g.cells(c1).arity, p1)(m.aload(c2))(m.iload(p2))
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
        m.aload(cells(c1)); setCell(g.cells(c1).arity, p1)(m.aload(cells(c2)))(m.iconst(p2))
        m.aload(cells(c2)); setCell(g.cells(c2).arity, p2)(m.aload(cells(c1)))(m.iconst(p1))
        if(p1 < 0 && p2 < 0)
          m.aload(ptw).aload(cells(c1)).invokevirtual(ptw_createCut)
      }
      (idx1, idx2) match {
        case (i1: FreeIdx, i2: FreeIdx) => connectFF(i1, i2)
        case (i1: FreeIdx, i2: CellIdx) => connectCF(i2, i1)
        case (i1: CellIdx, i2: FreeIdx) => connectCF(i1, i2)
        case (i1: CellIdx, i2: CellIdx) => connectCC(i1, i2)
      }
    }
    m.return_

    // statistics
    c.method(Acc.PUBLIC, "cellAllocationCount", tp.m().I).iconst(cellAllocations).ireturn
  }
}
