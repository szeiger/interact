package de.szeiger.interact.mt

import de.szeiger.interact.codegen.{AbstractCodeGen, LocalClassLoader}
import de.szeiger.interact.{CellIdx, Config, Connection, FreeIdx, RuleWiring}
import de.szeiger.interact.ast.Symbol
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

import scala.collection.mutable.ArrayBuffer

class CodeGen(genPackage: String, config: Config) extends AbstractCodeGen(config) {
  private val MAX_SPEC_CELL = 2
  private val interpreterPackage = "de/szeiger/interact/mt"
  private val riT = tp.c(s"$interpreterPackage/RuleImpl")
  private val wrT = tp.c(s"$interpreterPackage/WireRef")
  private val ptwT = tp.c(s"$interpreterPackage/PerThreadWorker")
  private val cellT = tp.c(s"$interpreterPackage/Cell")
  private val cellNT = tp.c(s"$interpreterPackage/CellN")
  private val cellSpecTs = (0 to MAX_SPEC_CELL).map(i => tp.c(s"$interpreterPackage/Cell$i"))
  private val cell_symId = cellT.method("symId", tp.m().I)
  private val cell_symIdSetter = cellT.method("symId_$eq", tp.m(tp.I).V)
  private val cell_auxRef = cellT.method("auxRef", tp.m(tp.I)(wrT))
  private val cell_pref = cellT.method("pref", tp.m()(wrT))
  private val cell_aref = (0 to MAX_SPEC_CELL).map { a =>
    (0 until a).map(p => cellSpecTs(a).method(s"aref$p", tp.m()(wrT)))
  }
  private val wr_cell = wrT.method("cell", tp.m()(cellT))
  private val wr_oppo = wrT.method("oppo", tp.m()(wrT))
  private val wr_resetPrincipalsUnsafe = wrT.method("resetPrincipalsUnsafe", tp.m(tp.I).V)
  private val ptw_connectFreeToFree = ptwT.method("connectFreeToFree", tp.m(wrT, wrT).V)
  private val ptw_connectAux = ptwT.method("connectAux", tp.m(wrT, cellT, tp.I).V)
  private val ptw_connectAuxSpec = (0 to MAX_SPEC_CELL).map { a =>
    (0 until a).map(p => ptwT.method(s"connectAux_${a}_$p", tp.m(wrT, cellSpecTs(a)).V))
  }
  private val ptw_connectPrincipal = ptwT.method("connectPrincipal", tp.m(wrT, cellT).V)
  private val ptw_createCut = ptwT.method("createCut", tp.m(wrT).V)
  private val ptw_deferredInc = ptwT.method("deferredInc", tp.m(wrT).V)
  private val new_CellN_II = cellNT.constr(tp.m(tp.I, tp.I).V)
  private val new_CellSpec_I = cellSpecTs.map(_.constr(tp.m(tp.I).V))
  private val new_WireRef_LILI = wrT.constr(tp.m(cellT, tp.I, cellT, tp.I).V)

  def compileRule(g: RuleWiring, cl: LocalClassLoader): RuleImplFactory[RuleImpl] = {
    val name1 = AbstractCodeGen.encodeName(g.sym1)
    val name2 = AbstractCodeGen.encodeName(g.sym2)
    val implClassName = s"$genPackage/Rule_$name1$$_$name2"
    val factClassName = s"$genPackage/RuleFactory_$name1$$_$name2"
    val syms = (Iterator.single(g.sym1) ++ g.branches.iterator.flatMap(_.cells)).distinct.toArray
    val sids = syms.iterator.zipWithIndex.toMap
    val (ric, sidFields) = createRuleClassBase(implClassName, sids)
    implementRuleClass(ric, sids, sidFields, g)
    val fac = createFactoryClass(ric, factClassName, syms.map(_.id))
    addClass(cl, ric)
    addClass(cl, fac)
    val c = cl.loadClass(fac.javaName)
    c.getDeclaredConstructor().newInstance().asInstanceOf[RuleImplFactory[RuleImpl]]
  }

  private def createFactoryClass(implClass: ClassDSL, factClassName: String, names: Seq[String]): ClassDSL = {
    val implClassT = implClass.thisClassTp
    val riFactoryT = tp.c[RuleImplFactory[_]]
    val sidLookupT = tp.i[SymbolIdLookup]
    val new_implClass = ConstructorRef(implClassT, tp.m(Seq.fill(names.length)(tp.I): _*).V)
    val sidLookup_getSymbolId = MethodRef(sidLookupT, "getSymbolId", tp.m(tp.c[String]).I)
    val c = DSL.newClass(Acc.PUBLIC.FINAL, factClassName, riFactoryT)
    c.emptyNoArgsConstructor(Acc.PUBLIC)
    val m = c.method(Acc.PUBLIC, "apply", tp.m(sidLookupT)(tp.c[Object]))
    val lookup = m.param("lookup", sidLookupT)
    m.newInitDup(new_implClass) {
      names.foreach { n => m.aload(lookup).ldc(n).invokeinterface(sidLookup_getSymbolId) }
    }
    m.areturn
    c
  }

  private def createRuleClassBase(implClassName: String, sids: Map[Symbol, Int]): (ClassDSL, IndexedSeq[FieldRef]) = {
    val sidCount = sids.size
    val c = DSL.newClass(Acc.PUBLIC.FINAL, implClassName, riT)
    val sidFields = for(i <- 0 until sidCount) yield c.field(Acc.PRIVATE | Acc.FINAL, s"sid$i", tp.I)

    // init
    {
      val m = c.constructor(Acc.PUBLIC, tp.m(Seq.fill(sidCount)(tp.I): _*))
      for(i <- 0 until sidCount) {
        val sid = m.param(s"sid$i", tp.I)
        m.aload(m.receiver).iload(sid).putfield(sidFields(i))
      }
      m.aload(m.receiver).invokespecial(c.superTp, "<init>", tp.m().V)
      m.return_
    }
    (c, sidFields)
  }

  protected def implementRuleClass(c: ClassDSL, sids: Map[Symbol, Int], sidFields: IndexedSeq[FieldRef], g: RuleWiring): Unit = {
    assert(g.branches.length == 1)
    val branch = g.branches.head
    val internalConns = branch.intConns.toArray
    val allConns = (branch.extConns ++ internalConns.iterator).toArray
    var cellAllocations, wireAllocations = 0

    val (reuse1, reuse2, fullReuseConn) = {
      val matchingArity1 = branch.cells.iterator.zipWithIndex.filter { case (sym, _) => sym.arity == g.sym1.arity }.map(_._2).toSet
      val matchingArity2 = branch.cells.iterator.zipWithIndex.filter { case (sym, _) => sym.arity == g.sym2.arity }.map(_._2).toSet
      val matchingSym1 = matchingArity1.filter(i => branch.cells(i) == g.sym1)
      val matchingSym2 = matchingArity2.filter(i => branch.cells(i) == g.sym2)
      val matchingSyms = matchingSym1 ++ matchingSym2
      // Find principal connection with both cut cells to reuse
      val fullReuseConn = internalConns.find {
        case Connection(i1: CellIdx, i2: CellIdx) =>
          matchingSyms.contains(i1.idx) && matchingSyms.contains(i2.idx) && i1 != i2 && (i1.port == -1 || i2.port == -1)
        case _ => false
      }.orNull
      val(reuse1, reuse2) = if(fullReuseConn != null) {
        val Connection(CellIdx(i1, _), CellIdx(i2, _)) = fullReuseConn
        if(branch.cells(i1) == g.sym1) (i1, i2) else (i2, i1)
      } else {
        // Find individual cells for reuse (with potential relabeling)
        val sameA = g.sym1.arity == g.sym2.arity
        var matchingArity1 = branch.cells.zipWithIndex.filter { case (sym, _) => sym.arity == g.sym1.arity }
        var matchingArity2 = branch.cells.zipWithIndex.filter { case (sym, _) => sym.arity == g.sym2.arity }
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
      //g.log()
      //println(s"reuse1: $reuse1, reuse2: $reuse2, fullReuse: $fullReuseConn")
      (reuse1, reuse2, fullReuseConn)
    }

    val needs1 = g.arity1 > 0 || reuse1 >= 0 || fullReuseConn == null // reuse lhs wr when not reusing full conn
    val needs2 = g.arity2 > 0 || reuse2 >= 0

    val m = c.method(Acc.PUBLIC, "reduce", tp.m(wrT, ptwT).V)
    val wr   = m.param("wr", wrT)
    val ptw  = m.param("ptw", ptwT)

    def getAuxRef(a: Int, p: Int): m.type = {
      if(a < cell_aref.length)
        m.invokevirtual(cell_aref(a)(p))
      else m.iconst(p).invokevirtual(cell_auxRef)
    }
    def ptwConnectLL(a: Int, p: Int): m.type = {
      if(p < 0) m.invokevirtual(ptw_connectPrincipal)
      else if(a < cell_aref.length)
        m.invokevirtual(ptw_connectAuxSpec(a)(p))
      else m.iconst(p).invokevirtual(ptw_connectAux)
    }
    def storeCastCell(name: String, arity: Int, start: Label = null): VarIdx = {
      if(arity < cellSpecTs.length) m.checkcast(cellSpecTs(arity))
      val v = m.storeLocal(cellT, name, start = start)
      v
    }

    val deferred = ArrayBuffer.empty[VarIdx]

    m.aload(wr).invokevirtual(wr_cell)
    val cut1 = m.storeLocal(cellT, "cut1")
    m.aload(wr).invokevirtual(wr_oppo).invokevirtual(wr_cell)
    val cut2 = m.storeLocal(cellT, "cut2")
    m.aload(cut1).invokevirtual(cell_symId)
    m.aload(m.receiver).getfield(sidFields(0))
    m.ifI_==.thnElse {
      if(needs1) m.aload(cut1)
      if(needs2) m.aload(cut2)
    } {
      if(needs1) m.aload(cut2)
      if(needs2) m.aload(cut1)
    }
    val l1 = m.newLabel
    val cRight = if(needs2) storeCastCell("cRight", g.arity2, start = l1) else VarIdx.none
    val cLeft = if(needs1) storeCastCell("cLeft", g.arity1, start = l1) else VarIdx.none
    m.setLabel(l1)
    val lhs = (0 until g.arity1).map { idx =>
      m.aload(cLeft)
      getAuxRef(g.arity1, idx)
      m.storeLocal(wrT, s"lhs$idx")
    }
    val rhs = (0 until g.arity2).map { idx =>
      m.aload(cRight)
      getAuxRef(g.arity2, idx)
      m.storeLocal(wrT, s"rhs$idx")
    }
    var reuseWire = if(fullReuseConn != null) VarIdx.none else m.aload(cLeft).invokevirtual(cell_pref).storeLocal(wrT)
    var reuseWireDeferred: (VarIdx, Int) = null

    def updateSym(cell: VarIdx, sym: Symbol): Unit = {
      m.aload(cell)
      m.aload(m.receiver).getfield(sidFields(sids(sym)))
      m.invokevirtual(cell_symIdSetter)
    }
    val cells = branch.cells.zipWithIndex.map {
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
        m.storeLocal(cellT, s"c$idx")
    }
    allConns.foreach { case conn @ Connection(idx1, idx2) =>
      def connectWW(i1: FreeIdx, i2: FreeIdx): Unit = {
        val l = if(i1.active == 1) rhs(i1.port) else lhs(i1.port)
        val r = if(i2.active == 1) rhs(i2.port) else lhs(i2.port)
        m.aload(ptw).aload(l).aload(r).invokevirtual(ptw_connectFreeToFree)
      }
      def connectWC(i1: FreeIdx, i2: CellIdx): Unit = {
        val skip1 = i2.idx == reuse1 && i1.active == 0 && i2.port == i1.port
        val skip2 = i2.idx == reuse2 && i1.active == 1 && i2.port == i1.port
        if((!skip1 && !skip2) || i2.port == -1) { //TODO: Allow i2.port == -1 and check for cut
          val l = if(i1.active == 1) rhs(i1.port) else lhs(i1.port)
          m.aload(ptw).aload(l).aload(cells(i2.idx))
          ptwConnectLL(branch.cells(i2.idx).arity, i2.port)
          if(i2.port < 0) deferred += l
        }
      }
      def connectCC(i1: CellIdx, i2: CellIdx): Unit = {
        def args = m.aload(cells(i1.idx)).iconst(i1.port).aload(cells(i2.idx)).iconst(i2.port)
        if(i1.port < 0 && i2.port < 0) {
          m.aload(ptw)
          wireAllocations += 1
          m.newInitDup(new_WireRef_LILI)(args)
          m.invokevirtual(ptw_createCut)
        } else {
          if(reuseWire != VarIdx.none) {
            val (c1, c2) = if(i1.port > i2.port) (i1, i2) else (i2, i1)
            m.aload(ptw).aload(reuseWire).aload(cells(c1.idx))
            ptwConnectLL(branch.cells(c1.idx).arity, c1.port)
            m.aload(ptw).aload(reuseWire).invokevirtual(wr_oppo).aload(cells(c2.idx))
            ptwConnectLL(branch.cells(c2.idx).arity, c2.port)
            reuseWireDeferred = (reuseWire, (if(i1.port < 0) 1 else 0) + (if(i2.port < 0) 1 else 0))
            reuseWire = VarIdx.none
          } else {
            wireAllocations += 1
            m.newInitConsume(new_WireRef_LILI)(args)
          }
        }
      }
      def reconnectPrimary(i1: CellIdx, i2: CellIdx): Unit = {
        //TODO: Fix pincipal handling for mt
        m.aload(ptw)
        m.aload(cells(i1.idx))
        if(i1.port < 0) m.invokevirtual(cell_pref)
        else getAuxRef(branch.cells(i1.idx).arity, i1.port)
        m.invokevirtual(wr_oppo)
        val o = m.dup.storeLocal(wrT)
        m.aload(cells(i2.idx))
        ptwConnectLL(branch.cells(i2.idx).arity, i2.port)
        reuseWireDeferred = (o, (if(i1.port < 0) 1 else 0) + (if(i2.port < 0) 1 else 0))
      }
      (idx1, idx2) match {
        case (i1: FreeIdx, i2: FreeIdx) => connectWW(i1, i2)
        case (i1: FreeIdx, i2: CellIdx) => connectWC(i1, i2)
        case (i1: CellIdx, i2: FreeIdx) => connectWC(i2, i1)
        case (i1: CellIdx, i2: CellIdx) if conn eq fullReuseConn =>
          if(i1.port == -1) reconnectPrimary(i1, i2)
          else reconnectPrimary(i2, i1)
        case (i1: CellIdx, i2: CellIdx) => connectCC(i1, i2)
      }
    }
    if(reuseWireDeferred != null) {
      val (w, p) = reuseWireDeferred
      m.aload(w).iconst(p).invokevirtual(wr_resetPrincipalsUnsafe)
      if(p == 2) m.aload(ptw).aload(w).invokevirtual(ptw_createCut)
    }
    deferred.foreach(w => m.aload(ptw).aload(w).invokevirtual(ptw_deferredInc))
    m.return_
    //g.log()
    //println(s"Cell allocations: $cellAllocations, wire allocations: $wireAllocations")

    // statistics
    c.method(Acc.PUBLIC, "cellAllocationCount", tp.m().I).iconst(cellAllocations).ireturn
    c.method(Acc.PUBLIC, "wireAllocationCount", tp.m().I).iconst(wireAllocations).ireturn
  }
}

trait SymbolIdLookup {
  def getSymbolId(name: String): Int
}

abstract class RuleImplFactory[T] {
  def apply(lookup: SymbolIdLookup): T
}
