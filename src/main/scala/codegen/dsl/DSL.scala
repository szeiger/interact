package de.szeiger.interact.codegen.dsl

import org.objectweb.asm.{ClassVisitor, Label, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.{AbstractInsnNode, FieldInsnNode, IincInsnNode, InsnNode, IntInsnNode, JumpInsnNode, LabelNode, LdcInsnNode, LineNumberNode, LookupSwitchInsnNode, MethodInsnNode, MultiANewArrayInsnNode, TableSwitchInsnNode, TryCatchBlockNode, TypeInsnNode, VarInsnNode}
import org.objectweb.asm.util.Printer

import scala.collection.mutable.ArrayBuffer

final class VarIdx(val idx: Int) extends AnyVal {
  def isDefined: Boolean = idx != -1
  def isEmpty: Boolean = idx == -1
}
object VarIdx {
  def none: VarIdx = new VarIdx(-1)
}

object DSL {
  def newClass(access: Acc, name: String, superTp: ClassOwner = ClassOwner[Object], interfaces: Array[String] = null, sourceFile: String = null): ClassDSL =
    new ClassDSL(access.SUPER, name, superTp, interfaces, sourceFile)
  def newInterface(access: Acc, name: String, interfaces: Array[String] = null, sourceFile: String = null): ClassDSL =
    new ClassDSL(access.INTERFACE.ABSTRACT, name, ClassOwner[Object], interfaces, sourceFile)
}

final class ClassDSL(access: Acc, val name: String, val superTp: ClassOwner = ClassOwner[Object],
  interfaces: Array[String] = null, sourceFile: String = null) {
  private[this] val fields = ArrayBuffer.empty[Field]
  private[this] val methods = ArrayBuffer.empty[MethodDSL]

  val thisTp: Owner = if(access.has(Acc.INTERFACE)) new InterfaceOwner(name) else new ClassOwner(name)
  def thisClassTp: ClassOwner = thisTp.asInstanceOf[ClassOwner]
  def thisInterfaceTp: InterfaceOwner = thisTp.asInstanceOf[InterfaceOwner]

  def javaName = name.replace('/', '.')

  private[this] class Field(val access: Acc, val name: String, val desc: ValDesc, val value: Any)

  def accept(v: ClassVisitor, version: Int = V1_8): Unit = {
    v.visit(version, access.acc, name, null, superTp.className, interfaces)
    if(sourceFile != null) v.visitSource(sourceFile, null)
    fields.foreach(f => v.visitField(f.access.acc, f.name, f.desc.desc, null, f.value))
    methods.foreach(_.accept(v, this))
    v.visitEnd()
  }

  def field(access: Acc, name: String, desc: ValDesc, value: Any): FieldRef = {
    val f = new Field(access, name, desc, value)
    fields.addOne(f)
    FieldRef(thisTp, name, desc)
  }
  def field(access: Acc, name: String, desc: ValDesc): FieldRef = field(access, name, desc, null)
  def field(access: Acc, ref: FieldRef, value: Any): FieldRef = field(access, ref.name, ref.desc, value)
  def field(access: Acc, ref: FieldRef): FieldRef = field(access, ref.name, ref.desc, null)

  def method(access: Acc, name: String, desc: MethodDesc): MethodDSL = {
    val m = new MethodDSL(access, name, desc)
    methods.addOne(m)
    m
  }

  def method(access: Acc, ref: MethodRef): MethodDSL = method(access, ref.name, ref.desc)

  def constructor(access: Acc, desc: Desc.MethodArgs): MethodDSL = method(access, "<init>", desc.V)

  def clinit(): MethodDSL = method(Acc.STATIC, "<clinit>", Desc.m().V)

  def emptyNoArgsConstructor(access: Acc = Acc.PUBLIC): MethodDSL = {
    val m = constructor(access, Desc.m())
    m.aload(m.receiver).invokespecial(superTp, "<init>", Desc.m().V)
    m.return_
  }

  def getter(field: FieldRef, access: Acc = Acc.PUBLIC.FINAL, _name: String = null): MethodDSL = {
    val name = if(_name == null) s"get${field.name.charAt(0).toUpper}${field.name.substring(1)}" else _name
    val m = method(access, name, Desc.m()(field.desc))
    m.aload(m.receiver).getfield(field).xreturn(field.desc)
  }

  def setter(field: FieldRef, access: Acc = Acc.PUBLIC.FINAL, _name: String = null): MethodDSL = {
    val name = if(_name == null) s"set${field.name.charAt(0).toUpper}${field.name.substring(1)}" else _name
    val m = method(access, name, Desc.m(field.desc).V)
    val p = m.param("value", field.desc, Acc.FINAL)
    m.aload(m.receiver).xload(p, field.desc).putfield(field).return_
  }
}

final class MethodDSL(access: Acc, val name: String, desc: MethodDesc) extends IfDSL { self =>
  protected[this] def ifEndLabel: Label = new Label
  protected[this] def method: MethodDSL = this

  private[this] val params = ArrayBuffer.empty[Local]
  private[this] val locals = ArrayBuffer.empty[Local]
  private[this] val code = ArrayBuffer.empty[AbstractInsnNode]
  private[this] val tryCatchBlocks = ArrayBuffer.empty[TryCatchBlockNode]
  private[this] class Local(val name: String, val desc: ValDesc, val access: Acc, val idx: Int, var start: Label, val end: Label) {
    var startPos: Int = -1
    override def toString: String = s"Label($name, $desc, $idx, $startPos, $start, $end)"
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
  def setLabel(l: Label = new Label): Label = { insn(new LabelNode(l)); l }

  def local(desc: ValDesc, name: String = null, start: Label = null, end: Label = this.end): VarIdx = {
    val idx = locals.length + argsCount - (if(isStatic) 1 else 0)
    val l = new Local(name, desc, Acc.none, idx, start, end)
    locals.addOne(l)
    new VarIdx(idx)
  }
  def storeLocal(desc: ValDesc, name: String = null, start: Label = null, end: Label = this.end): VarIdx = {
    val v = local(desc, name, start, end)
    xstore(v, desc)
    v
  }

  def accept(v: ClassVisitor, cls: ClassDSL): Unit = {
    val mv = v.visitMethod(access.acc, name, desc.desc, null, null)
    if(!access.has(Acc.ABSTRACT)) {
      assert(params.length == argsCount - 1)
      params.foreach(p => mv.visitParameter(p.name, p.access.acc))
      mv.visitCode()
      tryCatchBlocks.foreach(_.accept(mv))
      mv.visitLabel(start)
      code.zipWithIndex.foreach { case (in, idx) =>
        //System.err.println(s"emitting ${in.getOpcode} ${if(in.getOpcode >= 0 && in.getOpcode < Printer.OPCODES.length) Printer.OPCODES(in.getOpcode) else "???"}")
        in.accept(mv)
        in match {
          case in: VarInsnNode if in.getOpcode >= ISTORE && in.getOpcode <= SASTORE =>
            val v = if(isStatic) in.`var` + 1 else in.`var`
            if(v >= argsCount && v - argsCount < locals.length) {
              val l = locals(v-argsCount)
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
    }
    mv.visitEnd()
  }

  private[this] def storeVarInsn(opcode: Int, varIdx: VarIdx): this.type = {
    varInsn(opcode, varIdx)
    val idx = if(isStatic) varIdx.idx + 1 else varIdx.idx
    if(idx >= argsCount && idx - argsCount < locals.length) {
      val l = locals(idx - argsCount)
      if(l.startPos == -1) l.startPos = code.length
    }
    this
  }

  private[this] def insn(i: AbstractInsnNode): this.type = { code.addOne(i); this }
  private[this] def varInsn(opcode: Int, varIdx: VarIdx): this.type = { assert(varIdx != VarIdx.none); insn(new VarInsnNode(opcode, varIdx.idx)) }
  private[this] def insn(opcode: Int): this.type = insn(new InsnNode(opcode))
  private[this] def intInsn(opcode: Int, operand: Int): this.type = insn(new IntInsnNode(opcode, operand))
  private[dsl] def jumpInsn(opcode: Int, label: Label): this.type = insn(new JumpInsnNode(opcode, new LabelNode(label)))
  private[this] def fieldInsn(opcode: Int, owner: Owner, name: String, desc: ValDesc): this.type = insn(new FieldInsnNode(opcode, owner.className, name, desc.desc))
  private[this] def fieldInsn(opcode: Int, field: FieldRef): this.type = fieldInsn(opcode, field.owner, field.name, field.desc)
  private[this] def methodInsn(opcode: Int, owner: Owner, name: String, desc: MethodDesc): this.type = insn(new MethodInsnNode(opcode, owner.className, name, desc.desc, owner.isInterface))
  private[this] def methodInsn(opcode: Int, method: MethodRef): this.type = methodInsn(opcode, method.owner, method.name, method.desc)
  private[this] def methodInsn(opcode: Int, method: ConstructorRef): this.type = methodInsn(opcode, method.tpe, "<init>", method.desc)
  private[this] def typeInsn(opcode: Int, tpe: Owner): this.type = insn(new TypeInsnNode(opcode, tpe.className))

  def line(lineNumber: Int, l: Label = setLabel()): this.type = insn(new LineNumberNode(lineNumber, new LabelNode(l)))

  def aload(varIdx: VarIdx): this.type = varInsn(ALOAD, varIdx)
  def dload(varIdx: VarIdx): this.type = varInsn(DLOAD, varIdx)
  def fload(varIdx: VarIdx): this.type = varInsn(FLOAD, varIdx)
  def iload(varIdx: VarIdx): this.type = varInsn(ILOAD, varIdx)
  def lload(varIdx: VarIdx): this.type = varInsn(LLOAD, varIdx)

  def astore(varIdx: VarIdx): this.type = storeVarInsn(ASTORE, varIdx)
  def dstore(varIdx: VarIdx): this.type = storeVarInsn(DSTORE, varIdx)
  def fstore(varIdx: VarIdx): this.type = storeVarInsn(FSTORE, varIdx)
  def istore(varIdx: VarIdx): this.type = storeVarInsn(ISTORE, varIdx)
  def lstore(varIdx: VarIdx): this.type = storeVarInsn(LSTORE, varIdx)

  def aaload: this.type = insn(AALOAD)
  def baload: this.type = insn(BALOAD)
  def caload: this.type = insn(CALOAD)
  def daload: this.type = insn(DALOAD)
  def faload: this.type = insn(FALOAD)
  def iaload: this.type = insn(IALOAD)
  def laload: this.type = insn(LALOAD)
  def saload: this.type = insn(SALOAD)

  def aastore: this.type = insn(AASTORE)
  def bastore: this.type = insn(BASTORE)
  def castore: this.type = insn(CASTORE)
  def dastore: this.type = insn(DASTORE)
  def fastore: this.type = insn(FASTORE)
  def iastore: this.type = insn(IASTORE)
  def lastore: this.type = insn(LASTORE)
  def sastore: this.type = insn(SASTORE)

  def return_ : this.type = insn(RETURN)
  def areturn : this.type = insn(ARETURN)
  def dreturn : this.type = insn(DRETURN)
  def freturn : this.type = insn(FRETURN)
  def ireturn : this.type = insn(IRETURN)
  def lreturn : this.type = insn(LRETURN)

  def dadd: this.type = insn(DADD)
  def fadd: this.type = insn(FADD)
  def iadd: this.type = insn(IADD)
  def ladd: this.type = insn(LADD)
  def dmul: this.type = insn(DMUL)
  def fmul: this.type = insn(FMUL)
  def imul: this.type = insn(IMUL)
  def lmul: this.type = insn(LMUL)
  def dsub: this.type = insn(DSUB)
  def fsub: this.type = insn(FSUB)
  def isub: this.type = insn(ISUB)
  def lsub: this.type = insn(LSUB)
  def ddiv: this.type = insn(DDIV)
  def fdiv: this.type = insn(FDIV)
  def idiv: this.type = insn(IDIV)
  def ldiv: this.type = insn(LDIV)
  def dneg: this.type = insn(DNEG)
  def fneg: this.type = insn(FNEG)
  def ineg: this.type = insn(INEG)
  def lneg: this.type = insn(LNEG)
  def drem: this.type = insn(DREM)
  def frem: this.type = insn(FREM)
  def irem: this.type = insn(IREM)
  def lrem: this.type = insn(LREM)
  def ishl: this.type = insn(ISHL)
  def ishr: this.type = insn(ISHR)
  def iushr: this.type = insn(IUSHR)
  def lshl: this.type = insn(LSHL)
  def lshr: this.type = insn(LSHR)
  def lushr: this.type = insn(LUSHR)

  def iand: this.type = insn(IAND)
  def land: this.type = insn(LAND)
  def ior: this.type = insn(IOR)
  def lor: this.type = insn(LOR)
  def ixor: this.type = insn(IXOR)
  def lxor: this.type = insn(LXOR)

  def d2f: this.type = insn(D2F)
  def d2i: this.type = insn(D2I)
  def d2l: this.type = insn(D2L)
  def f2d: this.type = insn(F2D)
  def f2i: this.type = insn(F2I)
  def f2l: this.type = insn(F2L)
  def i2b: this.type = insn(I2B)
  def i2c: this.type = insn(I2C)
  def i2d: this.type = insn(I2D)
  def i2f: this.type = insn(I2F)
  def i2l: this.type = insn(I2L)
  def i2s: this.type = insn(I2S)
  def l2d: this.type = insn(L2D)
  def l2f: this.type = insn(L2F)
  def l2i: this.type = insn(L2I)

  def newarray(tp: ValDesc): this.type = tp.desc match {
    case "B" => intInsn(NEWARRAY, T_BYTE)
    case "Z" => intInsn(NEWARRAY, T_BOOLEAN)
    case "C" => intInsn(NEWARRAY, T_CHAR)
    case "I" => intInsn(NEWARRAY, T_INT)
    case "S" => intInsn(NEWARRAY, T_SHORT)
    case "D" => intInsn(NEWARRAY, T_DOUBLE)
    case "F" => intInsn(NEWARRAY, T_FLOAT)
    case "J" => intInsn(NEWARRAY, T_LONG)
    case s"L$s;" => typeInsn(ANEWARRAY, Desc.c(s)) // internal class name for classes
    case s => typeInsn(ANEWARRAY, Desc.c(s)) // descriptor for arrays
  }
  def multianewarray(tp: ValDesc, dims: Int): this.type = {
    assert(tp.isArray) // multianewarray expects the full array type, not its component type
    if(dims == 1) newarray(Desc.c(tp.desc.substring(1)))
    else insn(new MultiANewArrayInsnNode(tp.desc, dims))
  }

  def dup: this.type = insn(DUP)
  def dup_x1: this.type = insn(DUP_X1)
  def dup_x2: this.type = insn(DUP_X2)
  def dup2: this.type = insn(DUP2)
  def dup2_x1: this.type = insn(DUP2_X1)
  def dup2_x2: this.type = insn(DUP2_X2)
  def pop: this.type = insn(POP)
  def pop2: this.type = insn(POP2)
  def swap: this.type = insn(SWAP)

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

  def dconst(d: Double): this.type = d match {
    case 0 => insn(DCONST_0)
    case 1 => insn(DCONST_1)
    case _ => ldc(d)
  }

  def fconst(f: Float): this.type = f match {
    case 0 => insn(FCONST_0)
    case 1 => insn(FCONST_1)
    case 2 => insn(FCONST_2)
    case _ => ldc(f)
  }

  def lconst(l: Long): this.type = l match {
    case 0 => insn(LCONST_0)
    case 1 => insn(LCONST_1)
    case _ => ldc(l)
  }

  def const(value: Any): this.type = value match {
    case null => aconst_null
    case i: Int => iconst(i)
    case l: Long => lconst(l)
    case d: Double => dconst(d)
    case f: Float => fconst(f)
    case x => ldc(x)
  }

  def xreturn(tp: ValDesc) : this.type = tp.desc match {
    case "B" | "C" | "I" | "S" | "Z" => ireturn
    case "D" => dreturn
    case "F" => freturn
    case "J" => lreturn
    case _ => areturn
  }

  def xload(varIdx: VarIdx, tp: ValDesc) : this.type = tp.desc match {
    case "B" | "C" | "I" | "S" | "Z" => iload(varIdx)
    case "D" => dload(varIdx)
    case "F" => fload(varIdx)
    case "J" => lload(varIdx)
    case _ => aload(varIdx)
  }

  def xstore(varIdx: VarIdx, tp: ValDesc): this.type = tp.desc match {
    case "B" | "C" | "I" | "S" | "Z" => istore(varIdx)
    case "D" => dstore(varIdx)
    case "F" => fstore(varIdx)
    case "J" => lstore(varIdx)
    case _ => astore(varIdx)
  }

  def xaload(tp: ValDesc): this.type = tp.desc match {
    case "B" | "Z" => baload
    case "C" => caload
    case "I" => iaload
    case "S" => saload
    case "D" => daload
    case "F" => faload
    case "J" => laload
    case _ => aaload
  }

  def xastore(tp: ValDesc): this.type = tp.desc match {
    case "B" | "Z" => bastore
    case "C" => castore
    case "I" => iastore
    case "S" => sastore
    case "D" => dastore
    case "F" => fastore
    case "J" => lastore
    case _ => aastore
  }

  def dcmpg: this.type = insn(DCMPG)
  def dcmpl: this.type = insn(DCMPL)
  def fcmpg: this.type = insn(FCMPG)
  def fcmpl: this.type = insn(FCMPL)
  def lcmp: this.type = insn(LCMP)

  def ldc(value: Any): this.type = insn(new LdcInsnNode(value))
  def iinc(varIdx: VarIdx, incr: Int = 1): this.type = { assert(varIdx != VarIdx.none); insn(new IincInsnNode(varIdx.idx, incr)) }
  def arraylength: this.type = insn(ARRAYLENGTH)
  def athrow: this.type = insn(ATHROW)
  def monitorenter: this.type = insn(MONITORENTER)
  def monitorexit: this.type = insn(MONITOREXIT)

  def goto(l: Label): this.type = jumpInsn(GOTO, l)
  def if_icmpeq(l: Label): this.type = jumpInsn(IF_ICMPEQ, l)
  def if_icmpne(l: Label): this.type = jumpInsn(IF_ICMPNE, l)
  def if_acmpeq(l: Label): this.type = jumpInsn(IF_ACMPEQ, l)
  def if_acmpne(l: Label): this.type = jumpInsn(IF_ACMPNE, l)
  def if_icmpge(l: Label): this.type = jumpInsn(IF_ICMPGE, l)
  def if_icmpgt(l: Label): this.type = jumpInsn(IF_ICMPGT, l)
  def if_icmple(l: Label): this.type = jumpInsn(IF_ICMPLE, l)
  def if_icmplt(l: Label): this.type = jumpInsn(IF_ICMPLT, l)
  def ifeq(l: Label): this.type = jumpInsn(IFEQ, l)
  def ifne(l: Label): this.type = jumpInsn(IFNE, l)
  def iflt(l: Label): this.type = jumpInsn(IFLT, l)
  def ifgt(l: Label): this.type = jumpInsn(IFGT, l)
  def ifle(l: Label): this.type = jumpInsn(IFLE, l)
  def ifnull(l: Label): this.type = jumpInsn(IFNULL, l)
  def ifnonnull(l: Label): this.type = jumpInsn(IFNONNULL, l)

  def forRange(range: Range)(f: VarIdx => Unit): this.type = {
    val start, end = newLabel
    val i = iconst(range.start).storeLocal(Desc.I)
    setLabel(start)
    iload(i).iconst(range.end)
    if(range.step > 0) {
      if(range.isInclusive) if_icmpgt(end) else if_icmpge(end)
    } else {
      if(range.isInclusive) if_icmplt(end) else if_icmple(end)
    }
    f(i)
    iinc(i, range.step)
    goto(start)
    setLabel(end)
    this
  }

  def putfield(owner: Owner, name: String, desc: ValDesc): this.type = fieldInsn(PUTFIELD, owner, name, desc)
  def getfield(owner: Owner, name: String, desc: ValDesc): this.type = fieldInsn(GETFIELD, owner, name, desc)
  def putfield(field: FieldRef): this.type = fieldInsn(PUTFIELD, field)
  def getfield(field: FieldRef): this.type = fieldInsn(GETFIELD, field)
  def putstatic(owner: Owner, name: String, desc: ValDesc): this.type = fieldInsn(PUTSTATIC, owner, name, desc)
  def getstatic(owner: Owner, name: String, desc: ValDesc): this.type = fieldInsn(GETSTATIC, owner, name, desc)
  def putstatic(field: FieldRef): this.type = fieldInsn(PUTSTATIC, field)
  def getstatic(field: FieldRef): this.type = fieldInsn(GETSTATIC, field)

  def invokespecial(owner: Owner, name: String, desc: MethodDesc): this.type = methodInsn(INVOKESPECIAL, owner, name, desc)
  def invokespecial(method: MethodRef): this.type = methodInsn(INVOKESPECIAL, method)
  def invokespecial(method: ConstructorRef): this.type = methodInsn(INVOKESPECIAL, method)
  def invokestatic(owner: Owner, name: String, desc: MethodDesc): this.type = methodInsn(INVOKESTATIC, owner, name, desc)
  def invokestatic(method: MethodRef): this.type = methodInsn(INVOKESTATIC, method)
  def invokevirtual(owner: Owner, name: String, desc: MethodDesc): this.type = methodInsn(INVOKEVIRTUAL, owner, name, desc)
  def invokevirtual(method: MethodRef): this.type = methodInsn(INVOKEVIRTUAL, method)
  def invokeinterface(owner: Owner, name: String, desc: MethodDesc): this.type = methodInsn(INVOKEINTERFACE, owner, name, desc)
  def invokeinterface(method: MethodRef): this.type = methodInsn(INVOKEINTERFACE, method)
  //TODO: invokedynamic

  def invoke(method: MethodRef, targetTp: Owner = null): this.type = targetTp match {
    case null => invoke(method, method.owner)
    case tp: InterfaceOwner => invokeinterface(method.on(targetTp))
    case tp: ClassOwner => invokevirtual(method.on(targetTp))
  }

  def new_(tpe: Owner): this.type = typeInsn(NEW, tpe)
  def checkcast(tpe: Owner): this.type = typeInsn(CHECKCAST, tpe)
  def instanceof(tpe: Owner): this.type = typeInsn(INSTANCEOF, tpe)
  def nop: this.type = insn(NOP)

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

  def exceptionHandler(start: Label, end: Label, handler: Label, tpe: Owner = null): this.type = {
    val cls = if(tpe == null) null else tpe.className
    tryCatchBlocks += new TryCatchBlockNode(new LabelNode(start), new LabelNode(end), new LabelNode(handler), cls)
    this
  }
  def tryCatchGoto(tpe: Owner = null)(block: => Unit)(handler: => Unit): this.type = {
    val l1, l2, l3, l4 = newLabel
    exceptionHandler(l1, l2, l3, tpe)
    setLabel(l1)
    block
    setLabel(l2)
    goto(l4)
    setLabel(l3)
    handler
    setLabel(l4)
    this
  }

  def tableswitch(min: Int, max: Int, deflt: Label, labels: Seq[Label]): this.type =
    insn(new TableSwitchInsnNode(min, max, new LabelNode(deflt), labels.map(new LabelNode(_)): _*))
  def lookupswitch(keys: Array[Int], deflt: Label, labels: Seq[Label]): this.type =
    insn(new LookupSwitchInsnNode(new LabelNode(deflt), keys, labels.iterator.map(new LabelNode(_)).toArray))

  def tableSwitch(range: Range)(f: => Option[Int] => _): this.type = {
    val min = range.start
    val max = if(range.isInclusive) range.end else range.end-1
    assert(range.step == 1)
    val labels = (min to max).map(_ => newLabel)
    val deflt = newLabel
    tableswitch(min, max, deflt, labels)
    labels.zipWithIndex.foreach { case (l, i) =>
      setLabel(l)
      f(Some(min+i))
    }
    setLabel(deflt)
    f(None)
    this
  }
}

trait IfDSL {
  protected[this] def ifEndLabel: Label
  protected[this] def method: MethodDSL

  def if_==     : ThenDSL = new ThenDSL(IFEQ, IFNE, method, ifEndLabel)
  def if_!=     : ThenDSL = new ThenDSL(IFNE, IFEQ, method, ifEndLabel)
  def if_<      : ThenDSL = new ThenDSL(IFLT, IFGE, method, ifEndLabel)
  def if_>      : ThenDSL = new ThenDSL(IFGT, IFLE, method, ifEndLabel)
  def if_<=     : ThenDSL = new ThenDSL(IFLE, IFGT, method, ifEndLabel)
  def if_>=     : ThenDSL = new ThenDSL(IFGE, IFLT, method, ifEndLabel)

  def ifI_==    : ThenDSL = new ThenDSL(IF_ICMPEQ, IF_ICMPNE, method, ifEndLabel)
  def ifI_!=    : ThenDSL = new ThenDSL(IF_ICMPNE, IF_ICMPEQ, method, ifEndLabel)
  def ifI_<     : ThenDSL = new ThenDSL(IF_ICMPLT, IF_ICMPGE, method, ifEndLabel)
  def ifI_>     : ThenDSL = new ThenDSL(IF_ICMPGT, IF_ICMPLE, method, ifEndLabel)
  def ifI_<=    : ThenDSL = new ThenDSL(IF_ICMPLE, IF_ICMPGT, method, ifEndLabel)
  def ifI_>=    : ThenDSL = new ThenDSL(IF_ICMPGE, IF_ICMPLT, method, ifEndLabel)

  def ifA_==    : ThenDSL = new ThenDSL(IF_ACMPEQ, IF_ACMPNE, method, ifEndLabel)
  def ifA_!=    : ThenDSL = new ThenDSL(IF_ACMPNE, IF_ACMPEQ, method, ifEndLabel)
  def ifNull    : ThenDSL = new ThenDSL(IFNULL, IFNONNULL, method, ifEndLabel)
  def ifNonNull : ThenDSL = new ThenDSL(IFNONNULL, IFNULL, method, ifEndLabel)
}

final class ThenDSL(posOpcode: Int, negOpcode: Int, m: MethodDSL, l1: Label) {
  def and(load: => Unit): IfDSL = {
    m.jumpInsn(negOpcode, l1)
    load
    new IfDSL {
      protected[this] def ifEndLabel: Label = l1
      protected[this] def method: MethodDSL = m
    }
  }
  def thnElse(cont: => Unit)(skip: => Unit): MethodDSL = {
    val l2 = new Label
    m.jumpInsn(negOpcode, l1); cont; m.goto(l2)
    m.setLabel(l1); skip
    m.setLabel(l2)
    m
  }
  def thn(cont: => Unit): MethodDSL = {
    m.jumpInsn(negOpcode, l1)
    cont
    m.setLabel(l1)
    m
  }
  def jump(l: Label): MethodDSL = m.jumpInsn(posOpcode, l)
}
