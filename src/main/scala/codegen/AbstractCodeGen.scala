package de.szeiger.interact.codegen

import de.szeiger.interact.RulePlan
import de.szeiger.interact.ast.Symbol
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.util.{Textifier, TraceClassVisitor}
import org.objectweb.asm.{ClassReader, ClassWriter}

import java.io.{OutputStreamWriter, PrintWriter}

abstract class AbstractCodeGen[RI](protected val interpreterPackage: String, genPackage: String, logGenerated: Boolean) {
  protected val riT = tp.c(s"$interpreterPackage/RuleImpl")

  private def encodeName(s: String): String = {
    val b = new StringBuilder()
    s.foreach {
      case '|' => b.append("$bar")
      case '^' => b.append("$up")
      case '&' => b.append("$amp")
      case '<' => b.append("$less")
      case '>' => b.append("$greater")
      case ':' => b.append("$colon")
      case '+' => b.append("$plus")
      case '-' => b.append("$minus")
      case '*' => b.append("$times")
      case '/' => b.append("$div")
      case '%' => b.append("$percent")
      case c => b.append(c)
    }
    b.result()
  }

  def compile(g: RulePlan, cl: LocalClassLoader): RuleImplFactory[RI] = {
    val name1 = encodeName(g.sym1.id)
    val name2 = encodeName(g.sym2.id)
    val implClassName = s"$genPackage/Rule_$name1$$_$name2"
    val factClassName = s"$genPackage/RuleFactory_$name1$$_$name2"
    val syms = (Iterator.single(g.sym1) ++ g.branches.iterator.flatMap(_.cells)).distinct.toArray
    val sids = syms.iterator.zipWithIndex.toMap
    val (ric, sidFields) = createRuleClassBase(implClassName, riT, sids)
    implementRuleClass(ric, sids, sidFields, g)
    val fac = createFactoryClass(ric, factClassName, syms.map(_.id))
    def extName(n: String) = n.replace('/', '.')
    addClass(cl, extName(implClassName), ric)
    addClass(cl, extName(factClassName), fac)
    val c = cl.loadClass(fac.javaName)
    c.getDeclaredConstructor().newInstance().asInstanceOf[RuleImplFactory[RI]]
  }

  private def addClass(cl: LocalClassLoader, name: String, cls: ClassDSL): Unit = {
    val cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES)
    cls.accept(cw)
    val raw = cw.toByteArray
    if(logGenerated) {
      val cr = new ClassReader(raw)
      cr.accept(new TraceClassVisitor(cw, new Textifier(), new PrintWriter(new OutputStreamWriter(System.out))), 0)
    }
    cl.defineClass(name, raw)
  }

  protected def implementRuleClass(c: ClassDSL, sids: Map[Symbol, Int], sidFields: IndexedSeq[FieldRef], g: RulePlan): Unit

  private def createFactoryClass(implClass: ClassDSL, factClassName: String, names: Seq[String]): ClassDSL = {
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

  private def createRuleClassBase(implClassName: String, riT: ClassOwner, sids: Map[Symbol, Int]): (ClassDSL, IndexedSeq[FieldRef]) = {
    val sidCount = sids.size
    val c = new ClassDSL(Acc.PUBLIC | Acc.FINAL, implClassName, riT)
    val sidFields = for(i <- 0 until sidCount) yield c.field(Acc.PRIVATE | Acc.FINAL, s"sid$i", tp.I)
    val constrDesc = tp.m(Seq.fill(sidCount)(tp.I): _*).V
    var cellAllocations, wireAllocations = 0

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
    (c, sidFields)
  }
}

abstract class RuleImplFactory[T] {
  def apply(lookup: SymbolIdLookup): T
}

trait SymbolIdLookup {
  def getSymbolId(name: String): Int
}
