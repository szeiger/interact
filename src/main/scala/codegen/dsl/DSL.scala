package de.szeiger.interact.codegen.dsl

import org.objectweb.asm.{ClassVisitor, Label, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.{AbstractInsnNode, FieldInsnNode, IincInsnNode, InsnNode, IntInsnNode, JumpInsnNode, LabelNode, LdcInsnNode, LineNumberNode, MethodInsnNode, TableSwitchInsnNode, TryCatchBlockNode, TypeInsnNode, VarInsnNode}
import org.objectweb.asm.util.Printer

import scala.collection.mutable.ArrayBuffer

final class VarIdx(val idx: Int) extends AnyVal {
  def isDefined: Boolean = idx != -1
  def isEmpty: Boolean = idx == -1
}
object VarIdx {
  def none: VarIdx = new VarIdx(-1)
}

final class ClassDSL(access: Acc, val name: String, val superTp: ClassOwner = ClassOwner[Object],
  interfaces: Array[String] = null, sourceFile: String = null, version: Int = V1_8) {
  private[this] val fields = ArrayBuffer.empty[Field]
  private[this] val methods = ArrayBuffer.empty[MethodDSL]

  val thisTp: Owner = if(access.has(Acc.INTERFACE)) new InterfaceOwner(name) else new ClassOwner(name)
  def thisClassTp: ClassOwner = thisTp.asInstanceOf[ClassOwner]
  def thisInterfaceTp: InterfaceOwner = thisTp.asInstanceOf[InterfaceOwner]

  def javaName = name.replace('/', '.')

  private[this] class Field(val access: Acc, val name: String, val desc: ValDesc, val value: Any)

  def accept(v: ClassVisitor): Unit = {
    val effectiveAcc = if(access.has(Acc.INTERFACE)) access | Acc.ABSTRACT else access | Acc.SUPER
    v.visit(version, effectiveAcc.acc, name, null, superTp.className, interfaces)
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

  def getter(field: FieldRef, access: Acc = Acc.PUBLIC | Acc.FINAL, _name: String = null): MethodDSL = {
    val name = if(_name == null) s"get${field.name.charAt(0).toUpper}${field.name.substring(1)}" else _name
    val m = method(access, name, Desc.m()(field.desc))
    m.aload(m.receiver).getfield(field).genReturn(field.desc)
  }

  def setter(field: FieldRef, access: Acc = Acc.PUBLIC | Acc.FINAL, _name: String = null): MethodDSL = {
    val name = if(_name == null) s"set${field.name.charAt(0).toUpper}${field.name.substring(1)}" else _name
    val m = method(access, name, Desc.m(field.desc).V)
    val p = m.param("value", field.desc, Acc.FINAL)
    m.aload(m.receiver).genLoad(p, field.desc).putfield(field).return_
  }
}

final class MethodDSL(access: Acc, val name: String, desc: MethodDesc) {
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

  private[this] def store(v: VarIdx, desc: ValDesc): VarIdx = {
    desc.desc.charAt(0) match {
      case 'L' | '[' => astore(v)
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

  private[this] def stored(v: VarIdx): Unit = {
    val idx = if(isStatic) v.idx + 1 else v.idx
    if(idx >= argsCount && idx - argsCount < locals.length) {
      val l = locals(idx - argsCount)
      if(l.startPos == -1) l.startPos = code.length
    }
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
  private[this] def methodInsn(opcode: Int, method: ConstructorRef): this.type =
    methodInsn(opcode, method.tpe, "<init>", method.desc)
  private[this] def typeInsn(opcode: Int, tpe: Owner): this.type = insn(new TypeInsnNode(opcode, tpe.className))

  def line(lineNumber: Int, l: Label = setLabel()): this.type = insn(new LineNumberNode(lineNumber, new LabelNode(l)))

  def ldc(value: Any): this.type = insn(new LdcInsnNode(value))
  def iinc(varIdx: VarIdx, incr: Int = 1): this.type = { assert(varIdx != VarIdx.none); insn(new IincInsnNode(varIdx.idx, incr)) }

  def aload(varIdx: VarIdx): this.type = varInsn(ALOAD, varIdx)
  def dload(varIdx: VarIdx): this.type = varInsn(DLOAD, varIdx)
  def fload(varIdx: VarIdx): this.type = varInsn(FLOAD, varIdx)
  def iload(varIdx: VarIdx): this.type = varInsn(ILOAD, varIdx)
  def lload(varIdx: VarIdx): this.type = varInsn(LLOAD, varIdx)
  def astore(varIdx: VarIdx): this.type = { varInsn(ASTORE, varIdx); stored(varIdx); this }
  def dstore(varIdx: VarIdx): this.type = { varInsn(DSTORE, varIdx); stored(varIdx); this }
  def fstore(varIdx: VarIdx): this.type = { varInsn(FSTORE, varIdx); stored(varIdx); this }
  def istore(varIdx: VarIdx): this.type = { varInsn(ISTORE, varIdx); stored(varIdx); this }
  def lstore(varIdx: VarIdx): this.type = { varInsn(LSTORE, varIdx); stored(varIdx); this }

  def aaload: this.type = insn(AALOAD)
  def aastore: this.type = insn(AASTORE)
  def iaload: this.type = insn(IALOAD)
  def iastore: this.type = insn(IASTORE)

  def return_ : this.type = insn(RETURN)
  def areturn : this.type = insn(ARETURN)
  def dreturn : this.type = insn(DRETURN)
  def freturn : this.type = insn(FRETURN)
  def ireturn : this.type = insn(IRETURN)
  def lreturn : this.type = insn(LRETURN)
  def dup: this.type = insn(DUP)
  def dup_x1: this.type = insn(DUP_X1)
  def dup_x2: this.type = insn(DUP_X2)
  def pop: this.type = insn(POP)
  def pop2: this.type = insn(POP2)
  def swap: this.type = insn(SWAP)
  def ior: this.type = insn(IOR)
  def iand: this.type = insn(IAND)
  def ixor: this.type = insn(IXOR)
  def aconst_null: this.type = insn(ACONST_NULL)
  def iadd: this.type = insn(IADD)

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

  def genReturn(tp: ValDesc) : this.type = tp.desc match {
    case "B" | "C" | "I" | "S" | "Z" => ireturn
    case "D" => dreturn
    case "F" => freturn
    case "J" => lreturn
    case _ => areturn
  }

  def genLoad(varIdx: VarIdx, tp: ValDesc) : this.type = tp.desc match {
    case "B" | "C" | "I" | "S" | "Z" => iload(varIdx)
    case "D" => dload(varIdx)
    case "F" => fload(varIdx)
    case "J" => lload(varIdx)
    case _ => aload(varIdx)
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
  def ifeq(l: Label): this.type = jumpInsn(IFEQ, l)
  def ifne(l: Label): this.type = jumpInsn(IFNE, l)
  def iflt(l: Label): this.type = jumpInsn(IFLT, l)
  def ifgt(l: Label): this.type = jumpInsn(IFGT, l)
  def ifle(l: Label): this.type = jumpInsn(IFLE, l)
  def ifnull(l: Label): this.type = jumpInsn(IFNULL, l)
  def ifnonnull(l: Label): this.type = jumpInsn(IFNONNULL, l)

  private[this] def ifThenElse(opcode: Int, cont: => Unit, skip: => Unit): this.type = {
    val lElse, lEndif = new Label
    jumpInsn(opcode, lElse); cont; goto(lEndif)
    setLabel(lElse); skip
    setLabel(lEndif)
    this
  }
  private[this] def ifThen(opcode: Int, cont: => Unit): this.type = {
    val lEndif = new Label
    jumpInsn(opcode, lEndif)
    cont
    setLabel(lEndif)
    this
  }
  def ifThenI_== (cont: => Unit): this.type = ifThen(IF_ICMPNE, cont)
  def ifThenI_!= (cont: => Unit): this.type = ifThen(IF_ICMPEQ, cont)
  def ifThenI_< (cont: => Unit): this.type = ifThen(IF_ICMPGE, cont)
  def ifThenI_> (cont: => Unit): this.type = ifThen(IF_ICMPLE, cont)
  def ifThenI_<= (cont: => Unit): this.type = ifThen(IF_ICMPGT, cont)
  def ifThenI_>= (cont: => Unit): this.type = ifThen(IF_ICMPLT, cont)
  def if0Then_== (cont: => Unit): this.type = ifThen(IFNE, cont)
  def if0Then_!= (cont: => Unit): this.type = ifThen(IFEQ, cont)
  def if0Then_< (cont: => Unit): this.type = ifThen(IFGE, cont)
  def if0Then_> (cont: => Unit): this.type = ifThen(IFLE, cont)
  def if0Then_<= (cont: => Unit): this.type = ifThen(IFGT, cont)
  def if0Then_>= (cont: => Unit): this.type = ifThen(IFLT, cont)

  def ifThenElseI_== (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ICMPNE, cont, skip)
  def ifThenElseI_!= (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ICMPEQ, cont, skip)
  def ifThenElseI_< (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ICMPGE, cont, skip)
  def ifThenElseI_> (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ICMPLE, cont, skip)
  def ifThenElseI_<= (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ICMPGT, cont, skip)
  def ifThenElseI_>= (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ICMPLT, cont, skip)
  def if0ThenElse_== (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IFNE, cont, skip)
  def if0ThenElse_!= (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IFEQ, cont, skip)
  def if0ThenElse_< (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IFGE, cont, skip)
  def if0ThenElse_> (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IFLE, cont, skip)
  def if0ThenElse_<= (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IFGT, cont, skip)
  def if0ThenElse_>= (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IFLT, cont, skip)

  def ifThenA_== (cont: => Unit): this.type = ifThen(IF_ACMPNE, cont)
  def ifThenA_!= (cont: => Unit): this.type = ifThen(IF_ACMPEQ, cont)
  def ifNullThen (cont: => Unit): this.type = ifThen(IFNONNULL, cont)
  def ifNonNullThen (cont: => Unit): this.type = ifThen(IFNULL, cont)

  def ifThenElseA_== (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ACMPNE, cont, skip)
  def ifThenElseA_!= (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IF_ACMPEQ, cont, skip)
  def ifNullThenElse (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IFNONNULL, cont, skip)
  def ifNonNullThenElse (cont: => Unit)(skip: => Unit): this.type = ifThenElse(IFNULL, cont, skip)

  def forRange(from: Int, until: Int, incr: Int = 1)(f: VarIdx => Unit): this.type = {
    val start, end = newLabel
    val i = iconst(from).storeAnonLocal(Desc.I)
    setLabel(start)
    iload(i).iconst(until).if_icmpge(end)
    f(i)
    iinc(i, incr)
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

  def invoke(method: MethodRef, targetTp: Owner = null): this.type = targetTp match {
    case null => invoke(method, method.owner)
    case tp: InterfaceOwner => invokeinterface(method.on(targetTp))
    case tp: ClassOwner => invokevirtual(method.on(targetTp))
  }

  def new_(tpe: Owner): this.type = typeInsn(NEW, tpe)
  def checkcast(tpe: Owner): this.type = typeInsn(CHECKCAST, tpe)
  def instanceof(tpe: Owner): this.type = typeInsn(INSTANCEOF, tpe)

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
  def tableSwitch(min: Int, blocks: (() => _)*): this.type = {
    val labels = blocks.map(_ => newLabel)
    tableswitch(min, min+blocks.length-2, labels.last, labels.init)
    blocks.zip(labels).foreach { case (b, l) =>
      setLabel(l)
      b()
    }
    this
  }
}
