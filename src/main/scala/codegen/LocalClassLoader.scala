package de.szeiger.interact.codegen

import de.szeiger.interact.codegen.dsl.ClassDSL
import org.objectweb.asm.{ClassReader, ClassWriter}
import org.objectweb.asm.util.{Textifier, TraceClassVisitor}

import java.io.{OutputStreamWriter, PrintWriter}
import scala.collection.mutable

class LocalClassLoader(logGenerated: Boolean = false) extends ClassLoader {
  private[this] val builders = new mutable.HashMap[String, () => Array[Byte]]()

  override def findClass(className: String): Class[_] =
    builders.get(className).map { b =>
      val a = b()
      builders.remove(className)
      defineClass(className, a, 0, a.length)
    }.getOrElse(super.findClass(className))

  def add(name: String, build: () => ClassDSL): Unit = {
    val b: () => Array[Byte] = { () =>
      val cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES)
      build().accept(cw)
      val raw = cw.toByteArray
      if(logGenerated) {
        val cr = new ClassReader(raw)
        cr.accept(new TraceClassVisitor(cw, new Textifier(), new PrintWriter(new OutputStreamWriter(System.out))), 0)
      }
      raw
    }
    builders.put(name, b)
  }
}
