package de.szeiger.interact.codegen

import de.szeiger.interact.st2.RuleImpl
import org.objectweb.asm.{ClassWriter, Label}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.util.{Textifier, TraceClassVisitor}

import java.io.{OutputStreamWriter, PrintWriter}
import scala.collection.mutable

object CodeGen {
  def createAddZSampleGen(sid0: Int): RuleImpl = {
    val ric = new RuleImplClass("de/szeiger/interact/st2/AddZSampleGen", 1, "de/szeiger/interact/st2")
    ric.reduceAddZ()
    val cl = new LocalClassLoader
    cl.add(ric.c)
    val c = cl.loadClass("de.szeiger.interact.st2.AddZSampleGen")
    val cons = c.getDeclaredConstructor(classOf[Int])
    cons.newInstance(sid0).asInstanceOf[RuleImpl]
  }

  def createAddSSampleGen(sid0: Int, sid1: Int): RuleImpl = {
    val ric = new RuleImplClass("de/szeiger/interact/st2/AddSSampleGen", 2, "de/szeiger/interact/st2")
    ric.reduceAddS()
    val cl = new LocalClassLoader
    cl.add(ric.c)
    val c = cl.loadClass("de.szeiger.interact.st2.AddSSampleGen")
    val cons = c.getDeclaredConstructor(classOf[Int], classOf[Int])
    cons.newInstance(sid0, sid1).asInstanceOf[RuleImpl]
  }
}

class RuleImplClass(riClassName: String, sidCount: Int, interpreterPackage: String) {
  private[this] val wrOwner = new ClassOwner(s"$interpreterPackage/WireRef")
  private[this] val wrType = wrOwner.typeName
  private[this] val cellOwner = new ClassOwner(s"$interpreterPackage/Cell")
  private[this] val cellType = cellOwner.typeName
  private[this] val ptwOwner = new ClassOwner(s"$interpreterPackage/PerThreadWorker")
  private[this] val ptwType = ptwOwner.typeName

  val c = new ClassDSL(ACC_PUBLIC | ACC_FINAL, riClassName, s"$interpreterPackage/RuleImpl")
  for(i <- 0 until sidCount)
    c.field(ACC_PRIVATE | ACC_FINAL, s"sid$i", "I")

  // init
  {
    val m = c.method(ACC_PUBLIC, "<init>", s"(${"I" * sidCount})V")
    for(i <- 0 until sidCount) {
      val sid = m.param(s"sid$i", "I", ACC_FINAL)
      m.aload(m.receiver)
      m.iload(sid)
      m.putfield(riClassName, s"sid$i", "I")
    }
    m.aload(m.receiver)
    m.invokespecial(c.superOwner, "<init>", "()V")
    m.vreturn
  }

  def reduceAddZ(): Unit = {
    val m = c.method(ACC_PUBLIC, "reduce", s"($wrType$ptwType)V")
    val wr = m.param("wr", wrType, ACC_FINAL)
    val ptw = m.param("ptw", ptwType, ACC_FINAL)
    val l1, l2, l3, l4, l5, l6, l7 = new Label
    val c1 = m.local("c1", cellType, l1, m.end)
    val c2 = m.local("c2", cellType, l2, m.end)
    val cAdd = m.local("cAdd", cellType, l5, m.end)
    val y = m.local("y", wrType, l6, m.end)
    val r = m.local("r", wrType, l7, m.end)
    m.aload(wr)
    m.invokevirtual(wrOwner, "cell", s"()$cellType")
    m.astore(c1)
    m.label(l1)
    m.aload(wr)
    m.invokevirtual(wrOwner, "oppo", s"()$wrType")
    m.invokevirtual(wrOwner, "cell", s"()$cellType")
    m.astore(c2)
    m.label(l2)
    m.aload(c1)
    m.invokevirtual(cellOwner, "symId", "()I")
    m.aload(m.receiver)
    m.getfield(riClassName, "sid0", "I")
    m.if_icmpne(l3)
    m.aload(c1)
    m.goto(l4)
    m.label(l3)
    m.aload(c2)
    m.label(l4)
    m.astore(cAdd)
    m.label(l5)
    m.aload(cAdd)
    m.icons(0)
    m.invokevirtual(cellOwner, "auxRef", s"(I)$wrType")
    m.astore(y)
    m.label(l6)
    m.aload(cAdd)
    m.icons(1)
    m.invokevirtual(cellOwner, "auxRef", s"(I)$wrType")
    m.astore(r)
    m.label(l7)
    m.aload(ptw)
    m.aload(y)
    m.aload(r)
    m.invokevirtual(ptwOwner, "connectFreeToFree", s"($wrType$wrType)V")
    m.vreturn
  }

  def reduceAddS(): Unit = {
  }
}

class LocalClassLoader extends ClassLoader {
  val bytecode = new mutable.HashMap[String, Array[Byte]]()

  override def findClass(className: String): Class[_] =
    bytecode.get(className).map(a => defineClass(className, a, 0, a.length))
      .getOrElse(super.findClass(className))

  def add(cn: ClassDSL): Unit = {
    val cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES)
    cn.accept(cw)
    //val pr = new Textifier()
    //cn.accept(new TraceClassVisitor(cw, pr, new PrintWriter(new OutputStreamWriter(System.out))))
    bytecode.put(cn.name.replace('/', '.'), cw.toByteArray)
  }
}
