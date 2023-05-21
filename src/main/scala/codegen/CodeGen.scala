package de.szeiger.interact.codegen

import de.szeiger.interact.{CellIdx, Connection, FreeIdx, GenericRuleImpl, Symbol}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.{ClassReader, ClassWriter}
import org.objectweb.asm.util.{Textifier, TraceClassVisitor}

import java.io.{OutputStreamWriter, PrintWriter}
import scala.collection.mutable

class CodeGen[RI](interpreterPackage: String, genPackage: String) {
  private val riT = tp.c(s"$interpreterPackage/RuleImpl")
  private val wrT = tp.c(s"$interpreterPackage/WireRef")
  private val cellT = tp.c(s"$interpreterPackage/Cell")
  private val ptwT = tp.c(s"$interpreterPackage/PerThreadWorker")
  private val cell_symId = MethodRef(cellT, "symId", tp.m().I)
  private val cell_auxRef = MethodRef(cellT, "auxRef", tp.m(tp.I)(wrT))
  private val wr_cell = MethodRef(wrT, "cell", tp.m()(cellT))
  private val wr_oppo = MethodRef(wrT, "oppo", tp.m()(wrT))
  private val ptw_connectFreeToFree = MethodRef(ptwT, "connectFreeToFree", tp.m(wrT, wrT).V)
  private val ptw_connectAux = MethodRef(ptwT, "connectAux", tp.m(wrT, cellT, tp.I).V)
  private val ptw_connectPrincipal = MethodRef(ptwT, "connectPrincipal", tp.m(wrT, cellT).V)
  private val ptw_createCut = MethodRef(ptwT, "createCut", tp.m(wrT).V)
  private val new_Cell_II = ConstructorRef(cellT, tp.m(tp.I, tp.I).V)
  private val new_WireRef_LILI = ConstructorRef(wrT, tp.m(cellT, tp.I, cellT, tp.I).V)

  def createSample(name1: String, name2: String, names: Seq[String], _stub: Int): RuleImplFactory[RI] = {
    val implClassName = s"$genPackage/Rule$$$name1$$$name2"
    val factClassName = s"$genPackage/RuleFactory$$$name1$$$name2"
    val ric = createSampleRuleClass(implClassName, names, _stub)
    val fac = createFactoryClass(ric, factClassName, names)
    val cl = new LocalClassLoader
    cl.add(ric)
    cl.add(fac)
    val c = cl.loadClass(fac.javaName)
    c.getDeclaredConstructor().newInstance().asInstanceOf[RuleImplFactory[RI]]
  }

  def compile(g: GenericRuleImpl): RuleImplFactory[RI] = {
    val name1 = g.sym1.cons.name.s
    val name2 = g.sym2.cons.name.s
    val implClassName = s"$genPackage/Rule$$$name1$$$name2"
    val factClassName = s"$genPackage/RuleFactory$$$name1$$$name2"
    val syms = (Iterator.single(g.sym1) ++ g.cells.iterator).distinct.toArray
    val ric = createRuleClass(implClassName, syms.iterator.zipWithIndex.toMap, g)
    val fac = createFactoryClass(ric, factClassName, syms.map(_.cons.name.s))
    val cl = new LocalClassLoader
    cl.add(ric)
    cl.add(fac)
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
      val m = c.method(Acc.PUBLIC, "reduce", tp.m(wrT, ptwT).V)
      val wr   = m.param("wr", wrT, Acc.FINAL)
      val ptw  = m.param("ptw", ptwT, Acc.FINAL)
      m.aload(wr).invokevirtual(wr_cell)
      val cut1 = m.storeLocal("cut1", cellT, Acc.FINAL)
      m.aload(wr).invokevirtual(wr_oppo).invokevirtual(wr_cell)
      val cut2 = m.storeLocal("cut2", cellT, Acc.FINAL)
      m.aload(cut1).invokevirtual(cell_symId)
      m.aload(m.receiver).getfield(sidFields(0))
      m.ifElseI_== {
        if(g.arity1 > 0) m.aload(cut1)
        if(g.arity2 > 0) m.aload(cut2)
      } {
        if(g.arity1 > 0) m.aload(cut2)
        if(g.arity2 > 0) m.aload(cut1)
      }
      val l1 = m.newLabel
      val cRight = if(g.arity2 > 0) m.storeLocal("cRight", cellT, Acc.FINAL, start = l1) else VarIdx.none
      val cLeft = if(g.arity1 > 0) m.storeLocal("cLeft", cellT, Acc.FINAL, start = l1) else VarIdx.none
      m.label(l1)
      val lhs = (0 until g.arity1).map { idx =>
        m.aload(cLeft).iconst(idx).invokevirtual(cell_auxRef)
        m.storeLocal(s"lhs$idx", wrT, Acc.FINAL)
      }
      val rhs = (0 until g.arity2).map { idx =>
        m.aload(cRight).iconst(idx).invokevirtual(cell_auxRef)
        m.storeLocal(s"rhs$idx", wrT, Acc.FINAL)
      }
      val cells = g.cells.zipWithIndex.map { case (sym, idx) =>
        m.newInitDup(new_Cell_II) {
          m.aload(m.receiver).getfield(sidFields(sids(sym)))
          m.iconst(sym.arity)
        }.storeLocal(s"c$idx", cellT, Acc.FINAL)
      }
      (g.wireConnsDistinct ++ g.internalConns).foreach { case Connection(idx1, idx2) =>
        def connectWW(i1: FreeIdx, i2: FreeIdx): Unit = {
          val l = if(i1.rhs) rhs(i1.idx) else lhs(i1.idx)
          val r = if(i2.rhs) rhs(i2.idx) else lhs(i2.idx)
          m.aload(ptw).aload(l).aload(r).invokevirtual(ptw_connectFreeToFree)
        }
        def connectWC(i1: FreeIdx, i2: CellIdx): Unit = {
          val l = if(i1.rhs) rhs(i1.idx) else lhs(i1.idx)
          m.aload(ptw).aload(l).aload(cells(i2.idx))
          if(i2.port < 0) m.invokevirtual(ptw_connectPrincipal)
          else m.iconst(i2.port).invokevirtual(ptw_connectAux)
        }
        def connectCC(i1: CellIdx, i2: CellIdx): Unit = {
          def f = {
            m.aload(cells(i1.idx))
            m.iconst(i1.port)
            m.aload(cells(i2.idx))
            m.iconst(i2.port)
          }
          if(i1.port < 0 && i2.port < 0) {
            m.aload(ptw)
            m.newInitDup(new_WireRef_LILI)(f)
            m.invokevirtual(ptw_createCut)
          } else {
            m.newInitConsume(new_WireRef_LILI)(f)
          }
        }
        (idx1, idx2) match {
          case (i1: FreeIdx, i2: FreeIdx) => connectWW(i1, i2)
          case (i1: FreeIdx, i2: CellIdx) => connectWC(i1, i2)
          case (i1: CellIdx, i2: FreeIdx) => connectWC(i2, i1)
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

  def createSampleRuleClass(implClassName: String, names: Seq[String], _stub: Int): ClassDSL = {
    val sidCount = names.length
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

    def reduceAddZ(): Unit = {
      val m = c.method(Acc.PUBLIC, "reduce", tp.m(wrT, ptwT).V)
      val wr   = m.param("wr", wrT, Acc.FINAL)
      val ptw  = m.param("ptw", ptwT, Acc.FINAL)
      m.aload(wr).invokevirtual(wr_cell)
      val c1 = m.storeLocal("c1", cellT)
      m.aload(wr).invokevirtual(wr_oppo).invokevirtual(wr_cell)
      val c2 = m.storeLocal("c2", cellT)
      m.aload(c1).invokevirtual(cell_symId)
      m.aload(m.receiver).getfield(sidFields(0))
      m.ifElseI_== { m.aload(c1) } { m.aload(c2) }
      val cAdd = m.storeLocal("cAdd", cellT)
      m.aload(cAdd).iconst(0).invokevirtual(cell_auxRef)
      val y = m.storeLocal("y", wrT)
      m.aload(cAdd).iconst(1).invokevirtual(cell_auxRef)
      val r = m.storeLocal("r", wrT)
      m.aload(ptw).aload(y).aload(r).invokevirtual(ptw_connectFreeToFree)
      m.return_
    }

    def reduceAddS(): Unit = {
      val m = c.method(Acc.PUBLIC, "reduce", tp.m(wrT, ptwT).V)
      val wr    = m.param("wr", wrT, Acc.FINAL)
      val ptw   = m.param("ptw", ptwT, Acc.FINAL)
      m.aload(wr).invokevirtual(wr_cell)
      val c1 = m.storeLocal("c1", cellT, Acc.FINAL)
      m.aload(wr).invokevirtual(wr_oppo).invokevirtual(wr_cell)
      val c2 = m.storeLocal("c2", cellT, Acc.FINAL)
      m.aload(c1).invokevirtual(cell_symId)
      m.aload(m.receiver).getfield(sidFields(0))
      m.ifElseI_== { m.aload(c1).aload(c2) } { m.aload(c2).aload(c1) }
      val anon1 = m.anonLocal
      m.astore(anon1)
      val cAdd = m.storeLocal("cAdd", cellT, Acc.FINAL)
      m.aload(cAdd).iconst(0).invokevirtual(cell_auxRef)
      val y = m.storeLocal("y", wrT, Acc.FINAL)
      m.aload(cAdd).iconst(1).invokevirtual(cell_auxRef)
      val r = m.storeLocal("r", wrT, Acc.FINAL)
      m.aload(anon1).iconst(0).invokevirtual(cell_auxRef)
      val x = m.storeLocal("r", wrT, Acc.FINAL)
      m.newInitDup(new_Cell_II) {
        m.aload(m.receiver).getfield(sidFields(0))
        m.iconst(2)
      }
      val cAdd2 = m.storeLocal("cAdd2", cellT, Acc.FINAL)
      m.newInitDup(new_Cell_II) {
        m.aload(m.receiver).getfield(sidFields(1))
        m.iconst(1)
      }
      val cS2 = m.storeLocal("cS2", cellT, Acc.FINAL)
      m.aload(ptw).aload(y).aload(cS2).iconst(0).invokevirtual(ptw_connectAux)
      m.aload(ptw).aload(r).aload(cAdd2).iconst(1).invokevirtual(ptw_connectAux)
      m.newInitConsume(new_WireRef_LILI) {
        m.aload(cS2)
        m.iconst(-1)
        m.aload(cAdd2)
        m.iconst(0)
      }
      m.aload(ptw).aload(x).aload(cAdd2).invokevirtual(ptw_connectPrincipal)
      m.return_
    }

    _stub match {
      case 1 => reduceAddZ()
      case 2 => reduceAddS()
      case _ => ???
    }
    c
  }
}

class LocalClassLoader extends ClassLoader {
  val classes = new mutable.HashMap[String, Array[Byte]]()

  override def findClass(className: String): Class[_] =
    classes.get(className).map(a => defineClass(className, a, 0, a.length))
      .getOrElse(super.findClass(className))

  def add(cn: ClassDSL): Unit = {
    val cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES)
    cn.accept(cw)
    val raw = cw.toByteArray
    classes.put(cn.name.replace('/', '.'), raw)
    //val pr = new Textifier()
    //val cr = new ClassReader(raw)
    //cr.accept(new TraceClassVisitor(cw, pr, new PrintWriter(new OutputStreamWriter(System.out))), 0)
  }
}

abstract class RuleImplFactory[T] {
  def apply(lookup: SymbolIdLookup): T
}

trait SymbolIdLookup {
  def getSymbolId(name: String): Int
}
