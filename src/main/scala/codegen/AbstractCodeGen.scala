package de.szeiger.interact.codegen

import de.szeiger.interact.Config
import de.szeiger.interact.ast.Symbol
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import org.objectweb.asm.util.{CheckClassAdapter, Textifier, TraceClassVisitor}
import org.objectweb.asm.{ClassReader, ClassWriter => AClassWriter}

import java.io.{OutputStreamWriter, PrintWriter}
import java.util.zip.CRC32

abstract class AbstractCodeGen[RI](config: Config) {
  import AbstractCodeGen._

  private[this] def getCRC32(a: Array[Byte]): Long = {
    val crc = new CRC32
    crc.update(a)
    crc.getValue
  }

  protected def addClass(cl: ClassWriter, cls: ClassDSL): Unit = {
    val cw = new AClassWriter(AClassWriter.COMPUTE_FRAMES)
    val ca = new CheckClassAdapter(cw)
    cls.accept(ca)
    val raw = cw.toByteArray
    if(config.logCodeGenSummary) println(s"Generated class ${cls.name} (${raw.length} bytes, crc ${getCRC32(raw)})")
    if(config.logGeneratedClasses.exists(s => s == "*" || cls.name.contains(s))) {
      val cr = new ClassReader(raw)
      cr.accept(new TraceClassVisitor(cw, new Textifier(), new PrintWriter(new OutputStreamWriter(System.out))), 0)
    }
    cl.writeClass(cls.javaName, raw)
  }

  // Create a new Symbol instance that matches the given Symbol and place it on the stack
  protected def reifySymbol(m: MethodDSL, sym: Symbol): MethodDSL = {
    if(sym.isEmpty) m.invokestatic(symbol_NoSymbol)
    else m.newInitDup(new_Symbol) {
      m.ldc(sym.id).iconst(sym.arity).iconst(sym.returnArity)
      m.iconst(sym.payloadType.value).iconst(sym.matchContinuationPort)
      m.iconst(sym.flags)
    }
  }
}

object AbstractCodeGen {
  val symbolT = tp.c[Symbol]
  val symbol_NoSymbol = symbolT.method("NoSymbol", tp.m()(symbolT))
  val new_Symbol = symbolT.constr(tp.m(tp.c[String], tp.I, tp.I, tp.I, tp.I, tp.I).V)

  private[this] def encodeName(s: String): String = {
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

  def encodeName(s: Symbol): String = {
    assert(s.isDefined)
    encodeName(s.id)
  }
}
