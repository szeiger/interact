package de.szeiger.interact.codegen.dsl

import org.objectweb.asm.{ClassVisitor, Label, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.{AbstractInsnNode, FieldInsnNode, InsnNode, IntInsnNode, JumpInsnNode, LabelNode, LdcInsnNode, LineNumberNode, MethodInsnNode, TypeInsnNode, VarInsnNode}

import scala.collection.mutable.ArrayBuffer

final class VarIdx(val idx: Int) extends AnyVal
object VarIdx {
  def none: VarIdx = new VarIdx(-1)
}

class ClassDSL(access: Acc, val name: String, val superTp: ClassOwner = ClassOwner[Object],
  interfaces: Array[String] = null, sourceFile: String = null, version: Int = V1_8) {
  private[this] val fields = ArrayBuffer.empty[Field]
  private[this] val methods = ArrayBuffer.empty[MethodDSL]

  val thisTp: Owner = new ClassOwner(name)

  def javaName = name.replace('/', '.')

  private[this] class Field(val access: Acc, val name: String, val desc: ValDesc, val value: Any)

  def accept(v: ClassVisitor): Unit = {
    v.visit(version, ACC_SUPER | access.acc, name, null, superTp.className, interfaces)
    if(sourceFile != null) v.visitSource(sourceFile, null)
    fields.foreach(f => v.visitField(f.access.acc, f.name, f.desc.desc, null, f.value))
    methods.foreach(_.accept(v, this))
    v.visitEnd()
  }

  def field(access: Acc, name: String, desc: ValDesc, value: Any = null): FieldRef = {
    val f = new Field(access, name, desc, value)
    fields.addOne(f)
    FieldRef(thisTp, name, desc)
  }

  def method(access: Acc, name: String, desc: MethodDesc): MethodDSL = {
    val m = new MethodDSL(access, name, desc)
    methods.addOne(m)
    m
  }

  def emptyNoArgsConstructor(access: Acc): MethodDSL = {
    val m = method(Acc.PUBLIC, "<init>", Desc.m().V)
    m.aload(m.receiver).invokespecial(superTp, "<init>", Desc.m().V)
    m.return_
  }
}

class MethodDSL(access: Acc, name: String, desc: MethodDesc) {
  private[this] val params = ArrayBuffer.empty[Local]
  private[this] val locals = ArrayBuffer.empty[Local]
  private[this] val code = ArrayBuffer.empty[AbstractInsnNode]
  private[this] class Local(val name: String, val desc: ValDesc, val access: Acc, val idx: Int, var start: Label, val end: Label) {
    var startPos: Int = -1
    override def toString: String = s"Label($name, $desc, $idx, $startPos)"
  }
  private[this] def isStatic = access has Acc.STATIC
  private[this] val argsCount = Type.getArgumentsAndReturnSizes(desc.desc) >> 2

  val start, end = new Label
  def receiver: VarIdx =
    if(isStatic) throw new IllegalArgumentException("no receiver in static methods") else new VarIdx(0)

  def param(name: String, desc: ValDesc, access: Acc = Acc.none): VarIdx = {
    val l = new Local(name, desc, access, params.length + (if(isStatic) 0 else 1), start, end)
    params.addOne(l)
    new VarIdx(l.idx)
  }

  def newLabel: Label = new Label

  private[this] def store(v: VarIdx, desc: ValDesc): VarIdx = {
    desc.desc.charAt(0) match {
      case 'L' => astore(v)
      case 'I' => istore(v)
      case _ => ???
    }
    v
  }
  def local(name: String, desc: ValDesc, access: Acc = Acc.none, start: Label = null, end: Label = this.end): VarIdx = {
    val idx = locals.length + argsCount - (if(isStatic) 1 else 0)
    val l = new Local(name, desc, access, idx, start, end)
    locals.addOne(l)
    new VarIdx(idx)
  }
  def storeLocal(name: String, desc: ValDesc, access: Acc = Acc.none, start: Label = null, end: Label = this.end): VarIdx =
    store(local(name, desc, access, start, end), desc)
  def anonLocal: VarIdx = local(null, null)
  def storeAnonLocal(desc: ValDesc): VarIdx = storeLocal(null, desc)

  def accept(v: ClassVisitor, cls: ClassDSL): Unit = {
    val mv = v.visitMethod(access.acc, name, desc.desc, null, null)
    assert(params.length == argsCount - 1)
    params.foreach(p => mv.visitParameter(p.name, p.access.acc))
    mv.visitCode()
    mv.visitLabel(start)
    code.zipWithIndex.foreach { case (in, idx) =>
      //println(s"emitting ${in.getOpcode} ${if(in.getOpcode >= 0 && in.getOpcode < Printer.OPCODES.length) Printer.OPCODES(in.getOpcode) else "???"}")
      in.accept(mv)
      in match {
        case in: VarInsnNode if in.getOpcode >= ISTORE && in.getOpcode <= SASTORE =>
          val v = in.`var`
          if(v >= argsCount && v - argsCount < locals.length) {
            val l = locals(v-argsCount)
            //println(s"l: $l; idx: $idx")
            if(l.start == null && l.name != null && l.startPos == idx+1) {
              val ln = code(idx+1) match {
                case ln: LabelNode => ln
                case _ => val ln = new LabelNode; ln.accept(mv); ln
              }
              l.start = ln.getLabel
            }
          }
        case _ =>
      }
    }
    mv.visitLabel(end)
    if(!isStatic)
      mv.visitLocalVariable("this", s"L${cls.name};", null, start, end, 0)
    (params.iterator ++ locals.iterator).foreach { l =>
      if(l.name != null)
        mv.visitLocalVariable(l.name, l.desc.desc, null, l.start, l.end, l.idx)
    }
    mv.visitMaxs(0, 0) // ClassWriter.COMPUTE_FRAMES required
    mv.visitEnd()
  }

  private[this] def stored(v: VarIdx): Unit =
    if(v.idx >= argsCount && v.idx - argsCount < locals.length) {
      val l = locals(v.idx - argsCount)
      if(l.startPos == -1) l.startPos = code.length
    }

  private[this] def insn(i: AbstractInsnNode): this.type = { code.addOne(i); this }
  private[this] def varInsn(opcode: Int, varIdx: VarIdx): this.type = { assert(varIdx != VarIdx.none); insn(new VarInsnNode(opcode, varIdx.idx)) }
  private[this] def insn(opcode: Int): this.type = insn(new InsnNode(opcode))
  private[this] def intInsn(opcode: Int, operand: Int): this.type = insn(new IntInsnNode(opcode, operand))
  private[this] def jumpInsn(opcode: Int, label: Label): this.type = insn(new JumpInsnNode(opcode, new LabelNode(label)))
  private[this] def fieldInsn(opcode: Int, owner: Owner, name: String, desc: ValDesc): this.type =
    insn(new FieldInsnNode(opcode, owner.className, name, desc.desc))
  private[this] def fieldInsn(opcode: Int, field: FieldRef): this.type = fieldInsn(opcode, field.owner, field.name, field.desc)
  private[this] def methodInsn(opcode: Int, owner: Owner, name: String, desc: MethodDesc): this.type =
    insn(new MethodInsnNode(opcode, owner.className, name, desc.desc, owner.isInterface))
  private[this] def methodInsn(opcode: Int, method: MethodRef): this.type =
    methodInsn(opcode, method.owner, method.name, method.desc)
  private[this] def typeInsn(opcode: Int, tpe: Owner): this.type = insn(new TypeInsnNode(opcode, tpe.className))

  def label(l: Label): this.type = insn(new LabelNode(l))
  def line(lineNumber: Int, l: Label = null): this.type = {
    val l2 = if(l == null) {
      val l2 = new Label
      label(l2)
      l2
    } else l
    insn(new LineNumberNode(lineNumber, new LabelNode(l2)))
  }

  def ldc(value: Any): this.type = insn(new LdcInsnNode(value))

  def aload(varIdx: VarIdx): this.type = varInsn(ALOAD, varIdx)
  def astore(varIdx: VarIdx): this.type = { varInsn(ASTORE, varIdx); stored(varIdx); this }
  def iload(varIdx: VarIdx): this.type = varInsn(ILOAD, varIdx)
  def istore(varIdx: VarIdx): this.type = { varInsn(ISTORE, varIdx); stored(varIdx); this }

  def return_ : this.type = insn(RETURN)
  def areturn : this.type = insn(ARETURN)
  def ireturn : this.type = insn(IRETURN)
  def dup: this.type = insn(DUP)
  def dup_x1: this.type = insn(DUP_X1)
  def dup_x2: this.type = insn(DUP_X2)
  def pop: this.type = insn(POP)
  def swap: this.type = insn(SWAP)
  def ior: this.type = insn(IOR)
  def iand: this.type = insn(IAND)
  def ixor: this.type = insn(IXOR)
  def aconst_null: this.type = insn(ACONST_NULL)

  def iconst(i: Int): this.type = i match {
    case -1 => insn(ICONST_M1)
    case 0 => insn(ICONST_0)
    case 1 => insn(ICONST_1)
    case 2 => insn(ICONST_2)
    case 3 => insn(ICONST_3)
    case 4 => insn(ICONST_4)
    case 5 => insn(ICONST_5)
    case i if i >= Byte.MinValue && i <= Byte.MaxValue => intInsn(BIPUSH, i)
    case i if i >= Short.MinValue && i <= Short.MaxValue => intInsn(SIPUSH, i)
    case _ => ldc(i)
  }

  def goto(l: Label): this.type = jumpInsn(GOTO, l)
  def if_icmpeq(l: Label): this.type = jumpInsn(IF_ICMPEQ, l)
  def if_icmpne(l: Label): this.type = jumpInsn(IF_ICMPNE, l)
  def if_acmpeq(l: Label): this.type = jumpInsn(IF_ACMPEQ, l)
  def if_acmpne(l: Label): this.type = jumpInsn(IF_ACMPNE, l)
  def if_icmpge(l: Label): this.type = jumpInsn(IF_ICMPGE, l)
  def if_icmpgt(l: Label): this.type = jumpInsn(IF_ICMPGT, l)
  def if_icmple(l: Label): this.type = jumpInsn(IF_ICMPLE, l)
  def if_icmplt(l: Label): this.type = jumpInsn(IF_ICMPLT, l)

  private[this] def ifThenElse(opcode: Int, cont: => Unit, skip: => Unit): this.type = {
    val lElse, lEndif = new Label
    jumpInsn(opcode, lElse); cont; goto(lEndif)
    label(lElse); skip
    label(lEndif)
    this
  }
  private[this] def ifThen(opcode: Int, cont: => Unit): this.type = {
    val lEndif = new Label
    jumpInsn(opcode, lEndif)
    cont
    label(lEndif)
    this
  }
  def ifThenElseI_== (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ICMPNE, cont, skip)
  def ifThenElseI_!= (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ICMPEQ, cont, skip)
  def ifThenI_< (cont: => Unit): this.type = ifThen(IF_ICMPGE, cont)

  def putfield(owner: Owner, name: String, desc: ValDesc): this.type = fieldInsn(PUTFIELD, owner, name, desc)
  def getfield(owner: Owner, name: String, desc: ValDesc): this.type = fieldInsn(GETFIELD, owner, name, desc)
  def putfield(field: FieldRef): this.type = fieldInsn(PUTFIELD, field)
  def getfield(field: FieldRef): this.type = fieldInsn(GETFIELD, field)

  def invokespecial(owner: Owner, name: String, desc: MethodDesc): this.type = methodInsn(INVOKESPECIAL, owner, name, desc)
  def invokevirtual(owner: Owner, name: String, desc: MethodDesc): this.type = methodInsn(INVOKEVIRTUAL, owner, name, desc)
  def invokeinterface(owner: Owner, name: String, desc: MethodDesc): this.type = methodInsn(INVOKEINTERFACE, owner, name, desc)
  def invokespecial(method: MethodRef): this.type = methodInsn(INVOKESPECIAL, method)
  def invokevirtual(method: MethodRef): this.type = methodInsn(INVOKEVIRTUAL, method)
  def invokeinterface(method: MethodRef): this.type = methodInsn(INVOKEINTERFACE, method)

  def new_(tpe: Owner): this.type = typeInsn(NEW, tpe)
  def checkcast(tpe: Owner): this.type = typeInsn(CHECKCAST, tpe)

  def newInitDup(tpe: Owner, desc: MethodDesc)(f: => Unit): this.type = {
    new_(tpe)
    dup
    f
    invokespecial(tpe, "<init>", desc)
  }
  def newInitConsume(tpe: Owner, desc: MethodDesc)(f: => Unit): this.type = {
    new_(tpe)
    f
    invokespecial(tpe, "<init>", desc)
  }
  def invokeInit(cons: ConstructorRef): this.type = invokespecial(cons.tpe, "<init>", cons.desc)
  def newInitDup(cons: ConstructorRef)(f: => Unit): this.type = newInitDup(cons.tpe, cons.desc)(f)
  def newInitConsume(cons: ConstructorRef)(f: => Unit): this.type = newInitConsume(cons.tpe, cons.desc)(f)
}
