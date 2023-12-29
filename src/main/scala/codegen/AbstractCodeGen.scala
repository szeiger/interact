package de.szeiger.interact.codegen

import de.szeiger.interact.RulePlan
import de.szeiger.interact.ast.Symbol
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.util.{CheckClassAdapter, Textifier, TraceClassVisitor}
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

  protected def encodeName(s: Symbol): String = {
    assert(s.isDefined)
    encodeName(s.id)
  }

  protected def addClass(cl: LocalClassLoader, cls: ClassDSL): Unit = {
    val cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES)
    val ca = new CheckClassAdapter(cw)
    cls.accept(ca)
    val raw = cw.toByteArray
    if(logGenerated) {
      val cr = new ClassReader(raw)
      cr.accept(new TraceClassVisitor(cw, new Textifier(), new PrintWriter(new OutputStreamWriter(System.out))), 0)
    }
    cl.defineClass(cls.name.replace('/', '.'), raw)
  }
}

abstract class RuleImplFactory[T] {
  def apply(lookup: SymbolIdLookup): T
}

trait SymbolIdLookup {
  def getSymbolId(name: String): Int
}
