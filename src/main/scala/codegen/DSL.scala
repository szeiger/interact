package de.szeiger.interact.codegen

import org.objectweb.asm.{ClassVisitor, Label, Opcodes, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.{AbstractInsnNode, FieldInsnNode, InsnNode, IntInsnNode, JumpInsnNode, LabelNode, MethodInsnNode, VarInsnNode}

import scala.collection.mutable.ArrayBuffer

final class VarIdx(val idx: Int) extends AnyVal

sealed trait Owner {
  def className: String
  def isInterface: Boolean
  override def toString: String = className
  def typeName: String = s"L$className;"
}
class ClassOwner(val className: String) extends Owner {
  def isInterface = false
}
class InterfaceOwner(val className: String) extends Owner {
  def isInterface = false
}

class ClassDSL(access: Int, val name: String, superName: String = "java/lang/Object",
  interfaces: Array[String] = null, sourceFile: String = null) {
  private[this] val fields = ArrayBuffer.empty[Field]
  private[this] val methods = ArrayBuffer.empty[MethodDSL]

  val thisOwner: Owner = new ClassOwner(name)
  val superOwner: Owner = new ClassOwner(superName)

  private[this] class Field(val access: Int, val name: String, val desc: String, val value: Any)

  def accept(v: ClassVisitor): Unit = {
    v.visit(V1_8, ACC_SUPER | access, name, null, superName, interfaces)
    if(sourceFile != null) v.visitSource(sourceFile, null)
    fields.foreach(f => v.visitField(f.access, f.name, f.desc, null, f.value))
    methods.foreach(_.accept(v, this))
    v.visitEnd()
  }

  def field(access: Int, name: String, desc: String, value: Any = null): String = {
    val f = new Field(access, name, desc, value)
    fields.addOne(f)
    f.name
  }

  def method(access: Int, name: String, desc: String): MethodDSL = {
    val m = new MethodDSL(access, name, desc)
    methods.addOne(m)
    m
  }
}

class MethodDSL(access: Int, name: String, desc: String) {
  private[this] val params = ArrayBuffer.empty[Local]
  private[this] val locals = ArrayBuffer.empty[Local]
  private[this] val code = ArrayBuffer.empty[AbstractInsnNode]
  private[this] class Local(val name: String, val desc: String, val access: Int, val idx: Int, val start: Label, val end: Label)
  private[this] def isStatic = (access & ACC_STATIC) != 0
  private[this] val argsCount = Type.getArgumentsAndReturnSizes(desc) >> 2

  val start, end = new Label
  def receiver: VarIdx =
    if(isStatic) throw new IllegalArgumentException("no receiver in static methods") else new VarIdx(0)

  def param(name: String, desc: String, access: Int = 0): VarIdx = {
    val l = new Local(name, desc, access, params.length + (if(isStatic) 0 else 1), start, end)
    params.addOne(l)
    new VarIdx(l.idx)
  }

  def local(name: String, desc: String, start: Label, end: Label): VarIdx = {
    val idx = locals.length + argsCount - (if(isStatic) 1 else 0)
    val l = new Local(name, desc, 0, idx, start, end)
    locals.addOne(l)
    new VarIdx(idx)
  }

  def accept(v: ClassVisitor, cls: ClassDSL): Unit = {
    val mv = v.visitMethod(access, name, desc, null, null)
    assert(params.length == argsCount - 1)
    params.foreach(p => mv.visitParameter(p.name, p.access))
    mv.visitCode()
    mv.visitLabel(start)
    code.foreach(_.accept(mv))
    mv.visitLabel(end)
    if(!isStatic)
      mv.visitLocalVariable("this", s"L${cls.name};", null, start, end, 0)
    (params.iterator ++ locals.iterator).foreach(p => mv.visitLocalVariable(p.name, p.desc, null, p.start, p.end, p.idx))
    mv.visitMaxs(0, 0) // ClassWriter.COMPUTE_FRAMES required
    mv.visitEnd()
  }

  def label(l: Label) = code.addOne(new LabelNode(l))
  def aload(varIdx: VarIdx): Unit = code.addOne(new VarInsnNode(Opcodes.ALOAD, varIdx.idx))
  def astore(varIdx: VarIdx): Unit = code.addOne(new VarInsnNode(Opcodes.ASTORE, varIdx.idx))
  def iload(varIdx: VarIdx): Unit = code.addOne(new VarInsnNode(Opcodes.ILOAD, varIdx.idx))
  def istore(varIdx: VarIdx): Unit = code.addOne(new VarInsnNode(Opcodes.ISTORE, varIdx.idx))
  def vreturn: Unit = code.addOne(new InsnNode(Opcodes.RETURN))
  def icons(i: Int): Unit = code.addOne(i match {
    case -1 => new InsnNode(Opcodes.ICONST_M1)
    case 0 => new InsnNode(Opcodes.ICONST_0)
    case 1 => new InsnNode(Opcodes.ICONST_1)
    case 2 => new InsnNode(Opcodes.ICONST_2)
    case 3 => new InsnNode(Opcodes.ICONST_3)
    case 4 => new InsnNode(Opcodes.ICONST_4)
    case 5 => new InsnNode(Opcodes.ICONST_5)
    case i if i >= Byte.MinValue && i <= Byte.MaxValue => new IntInsnNode(Opcodes.BIPUSH, i)
    case i if i >= Short.MinValue && i <= Short.MaxValue => new IntInsnNode(Opcodes.SIPUSH, i)
    case _ => ???
  })
  def goto(l: Label): Unit = code.addOne(new JumpInsnNode(Opcodes.GOTO, new LabelNode(l)))
  def if_icmpne(l: Label): Unit = code.addOne(new JumpInsnNode(Opcodes.IF_ICMPNE, new LabelNode(l)))
  def putfield(owner: String, name: String, desc: String): Unit =
    code.addOne(new FieldInsnNode(Opcodes.PUTFIELD, owner, name, desc))
  def getfield(owner: String, name: String, desc: String): Unit =
    code.addOne(new FieldInsnNode(Opcodes.GETFIELD, owner, name, desc))
  def invokespecial(owner: Owner, name: String, desc: String): Unit =
    code.addOne(new MethodInsnNode(Opcodes.INVOKESPECIAL, owner.className, name, desc, owner.isInterface))
  def invokevirtual(owner: Owner, name: String, desc: String): Unit =
    code.addOne(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, owner.className, name, desc, owner.isInterface))
}
