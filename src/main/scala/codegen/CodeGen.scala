package de.szeiger.interact.codegen

import de.szeiger.interact.{CellIdx, Connection, FreeIdx, GenericRuleImpl, RuleImplFactory, Symbol, SymbolIdLookup}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.Label

class CodeGen[RI](interpreterPackage: String, genPackage: String) {
  private val MAX_SPEC_CELL = 2
  private val riT = tp.c(s"$interpreterPackage/RuleImpl")
  private val wrT = tp.c(s"$interpreterPackage/WireRef")
  private val cellT = tp.c(s"$interpreterPackage/Cell")
  private val cellNT = tp.c(s"$interpreterPackage/CellN")
  private val cellSpecTs = (0 to MAX_SPEC_CELL).map(i => tp.c(s"$interpreterPackage/Cell$i"))
  private val ptwT = tp.c(s"$interpreterPackage/PerThreadWorker")
  private val cell_symId = MethodRef(cellT, "symId", tp.m().I)
  private val cell_auxRef = MethodRef(cellT, "auxRef", tp.m(tp.I)(wrT))
  private val cell_pref = MethodRef(cellT, "pref", tp.m()(wrT))
  private val cell_aref = (0 to MAX_SPEC_CELL).map { a =>
    (0 until a).map(p => MethodRef(cellSpecTs(a), s"aref$p", tp.m()(wrT)))
  }
  private val wr_cell = MethodRef(wrT, "cell", tp.m()(cellT))
  private val wr_oppo = MethodRef(wrT, "oppo", tp.m()(wrT))
  private val wr_reconnect = MethodRef(wrT, "reconnect", tp.m(cellT, tp.I, cellT, tp.I).V)
  private val ptw_connectFreeToFree = MethodRef(ptwT, "connectFreeToFree", tp.m(wrT, wrT).V)
  private val ptw_connectAux = MethodRef(ptwT, "connectAux", tp.m(wrT, cellT, tp.I).V)
  private val ptw_connectAuxSpec = (0 to MAX_SPEC_CELL).map { a =>
    (0 until a).map(p => MethodRef(ptwT, s"connectAux_${a}_$p", tp.m(wrT, cellSpecTs(a)).V))
  }
  private val ptw_connectPrincipal = MethodRef(ptwT, "connectPrincipal", tp.m(wrT, cellT).V)
  private val ptw_createCut = MethodRef(ptwT, "createCut", tp.m(wrT).V)
  private val new_CellN_II = ConstructorRef(cellNT, tp.m(tp.I, tp.I).V)
  private val new_CellSpec_I = cellSpecTs.map(t => ConstructorRef(t, tp.m(tp.I).V))
  private val new_WireRef_LILI = ConstructorRef(wrT, tp.m(cellT, tp.I, cellT, tp.I).V)

  def compile(g: GenericRuleImpl, cl: LocalClassLoader): RuleImplFactory[RI] = {
    val name1 = g.sym1.cons.name.s
    val name2 = g.sym2.cons.name.s
    val implClassName = s"$genPackage/Rule$$$name1$$$name2"
    val factClassName = s"$genPackage/RuleFactory$$$name1$$$name2"
    val syms = (Iterator.single(g.sym1) ++ g.cells.iterator).distinct.toArray
    val ric = createRuleClass(implClassName, syms.iterator.zipWithIndex.toMap, g)
    val fac = createFactoryClass(ric, factClassName, syms.map(_.cons.name.s))
    def extName(n: String) = n.replace('/', '.')
    cl.add(extName(implClassName), () => ric)
    cl.add(extName(factClassName), () => fac)
    val c = cl.loadClass(fac.javaName)
    c.getDeclaredConstructor().newInstance().asInstanceOf[RuleImplFactory[RI]]
  }

  def createRuleClass(implClassName: String, sids: Map[Symbol, Int], g: GenericRuleImpl): ClassDSL = {
    val sidCount = sids.size
    val c = new ClassDSL(Acc.PUBLIC | Acc.FINAL, implClassName, riT)
    val sidFields = for(i <- 0 until sidCount) yield c.field(Acc.PRIVATE | Acc.FINAL, s"sid$i", tp.I)
    val constrDesc = tp.m(Seq.fill(sidCount)(tp.I): _*).V

    // init
    {
      val m = c.method(Acc.PUBLIC, "<init>", constrDesc)
      for(i <- 0 until sidCount) {
        val sid = m.param(s"sid$i", tp.I, Acc.FINAL)
        m.aload(m.receiver).iload(sid).putfield(sidFields(i))
      }
      m.aload(m.receiver).invokespecial(c.superTp, "<init>", tp.m().V)
      m.return_
    }

    // reduce
    {
      val reuse1 = g.cells.indexOf(g.sym1)
      val reuse2 = g.cells.indexOf(g.sym2)
      val internalConns = g.internalConns.toArray
      val reuseCandidates = internalConns.filter {
        case Connection(i1: CellIdx, i2: CellIdx) => (i1.idx == reuse1 && i2.idx == reuse2) || (i1.idx == reuse2 && i2.idx == reuse1)
        case _ => false
      }
      val primaryReuse = reuseCandidates.find { case Connection(i1: CellIdx, i2: CellIdx) =>
        i1.port == -1 || i2.port == -1
      }.getOrElse(null)
      val needs1 = g.arity1 > 0 || reuse1 >= 0 || primaryReuse == null
      val needs2 = g.arity2 > 0 || reuse2 >= 0
      //println(s"reuse1: $reuse1, reuse2: $reuse2, primaryReuse: $primaryReuse")
      //if(reuseCandidates.nonEmpty && primaryReuse == null)
      //  println("no primary reuse")
      val m = c.method(Acc.PUBLIC, "reduce", tp.m(wrT, ptwT).V)
      val wr   = m.param("wr", wrT, Acc.FINAL)
      val ptw  = m.param("ptw", ptwT, Acc.FINAL)

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
        val v = m.storeLocal(name, cellT, Acc.FINAL, start = start)
        v
      }

      m.aload(wr).invokevirtual(wr_cell)
      val cut1 = m.storeLocal("cut1", cellT, Acc.FINAL)
      m.aload(wr).invokevirtual(wr_oppo).invokevirtual(wr_cell)
      val cut2 = m.storeLocal("cut2", cellT, Acc.FINAL)
      m.aload(cut1).invokevirtual(cell_symId)
      m.aload(m.receiver).getfield(sidFields(0))
      m.ifElseI_== {
        if(needs1) m.aload(cut1)
        if(needs2) m.aload(cut2)
      } {
        if(needs1) m.aload(cut2)
        if(needs2) m.aload(cut1)
      }
      val l1 = m.newLabel
      val cRight = if(needs2) storeCastCell("cRight", g.arity2, start = l1) else VarIdx.none
      val cLeft = if(needs1) storeCastCell("cLeft", g.arity1, start = l1) else VarIdx.none
      m.label(l1)
      val lhs = (0 until g.arity1).map { idx =>
        m.aload(cLeft)
        getAuxRef(g.arity1, idx)
        m.storeLocal(s"lhs$idx", wrT, Acc.FINAL)
      }
      val rhs = (0 until g.arity2).map { idx =>
        m.aload(cRight)
        getAuxRef(g.arity2, idx)
        m.storeLocal(s"rhs$idx", wrT, Acc.FINAL)
      }
      var reuseWire = if(primaryReuse != null) VarIdx.none else m.aload(cLeft).invokevirtual(cell_pref).storeAnonLocal(wrT)

      val cells = g.cells.zipWithIndex.map {
        case (_, idx) if idx == reuse1 => cLeft
        case (_, idx) if idx == reuse2 => cRight
        case (sym, idx) =>
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
      (g.wireConnsDistinct ++ internalConns.iterator).foreach { case conn @ Connection(idx1, idx2) =>
        def connectWW(i1: FreeIdx, i2: FreeIdx): Unit = {
          val l = if(i1.rhs) rhs(i1.idx) else lhs(i1.idx)
          val r = if(i2.rhs) rhs(i2.idx) else lhs(i2.idx)
          m.aload(ptw).aload(l).aload(r).invokevirtual(ptw_connectFreeToFree)
        }
        def connectWC(i1: FreeIdx, i2: CellIdx): Unit = {
          val l = if(i1.rhs) rhs(i1.idx) else lhs(i1.idx)
          m.aload(ptw).aload(l).aload(cells(i2.idx))
          ptwConnectLL(g.cells(i2.idx).arity, i2.port)
        }
        def connectCC(i1: CellIdx, i2: CellIdx): Unit = {
          def args = m.aload(cells(i1.idx)).iconst(i1.port).aload(cells(i2.idx)).iconst(i2.port)
          if(i1.port < 0 && i2.port < 0) {
            m.aload(ptw)
            m.newInitDup(new_WireRef_LILI)(args)
            m.invokevirtual(ptw_createCut)
          } else {
            if(reuseWire != VarIdx.none) {
              m.aload(reuseWire)
              args
              m.invokevirtual(wr_reconnect)
              reuseWire = VarIdx.none
            } else m.newInitConsume(new_WireRef_LILI)(args)
          }
        }
        def reconnectPrimary(i1: CellIdx, i2: CellIdx): Unit = {
          m.aload(ptw)
          //TODO: Fix pincipal handling for mt
          m.aload(cells(i1.idx))
          if(i1.port < 0) m.invokevirtual(cell_pref)
          else getAuxRef(g.cells(i1.idx).arity, i1.port)
          m.invokevirtual(wr_oppo)
          m.aload(cells(i2.idx))
          ptwConnectLL(g.cells(i2.idx).arity, i2.port)
        }
        (idx1, idx2) match {
          case (i1: FreeIdx, i2: FreeIdx) => connectWW(i1, i2)
          case (i1: FreeIdx, i2: CellIdx) => connectWC(i1, i2)
          case (i1: CellIdx, i2: FreeIdx) => connectWC(i2, i1)
          case (i1: CellIdx, i2: CellIdx) if conn eq primaryReuse =>
            if(i1.port == -1) reconnectPrimary(i1, i2)
            else reconnectPrimary(i2, i1)
          case (i1: CellIdx, i2: CellIdx) => connectCC(i2, i1)
        }
      }
      m.return_
    }
    c
  }

  def createFactoryClass(implClass: ClassDSL, factClassName: String, names: Seq[String]): ClassDSL = {
    val implClassT = implClass.thisTp
    val riFactoryT = tp.c[RuleImplFactory[_]]
    val sidLookupT = tp.i[SymbolIdLookup]
    val new_implClass = ConstructorRef(implClassT, tp.m(Seq.fill(names.length)(tp.I): _*).V)
    val sidLookup_getSymbolId = MethodRef(sidLookupT, "getSymbolId", tp.m(tp.c[String]).I)
    val c = new ClassDSL(Acc.PUBLIC | Acc.FINAL, factClassName, riFactoryT)
    c.emptyNoArgsConstructor(Acc.PUBLIC)
    val m = c.method(Acc.PUBLIC, "apply", tp.m(sidLookupT)(tp.c[Object]))
    val lookup = m.param("lookup", sidLookupT, Acc.FINAL)
    m.newInitDup(new_implClass) {
      names.foreach { n => m.aload(lookup).ldc(n).invokeinterface(sidLookup_getSymbolId) }
    }
    m.areturn
    c
  }
}
