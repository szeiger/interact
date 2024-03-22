package de.szeiger.interact.codegen.dsl

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Label

object TypedDSL {
  def apply(d: ValDesc, m: MethodDSL): TypedDSL = d.desc match {
    case "I" => new IntTypedDSL(m)
    case "J" => new LongTypedDSL(m)
    case "F" => new FloatTypedDSL(m)
    case "D" => new DoubleTypedDSL(m)
    case _ if d.isClass || d.isArray => new RefTypedDSL(m, d)
  }
}

abstract class TypedDSL(m: MethodDSL) {
  def desc: ValDesc
  def wide: Boolean
  def xload(v: VarIdx): this.type
  def xstore(v: VarIdx): this.type
  def xaload: this.type
  def xastore: this.type
  def xreturn: this.type
  def zero: this.type
  def xdup: this.type = { if(wide) m.dup2 else m.dup; this }
  def xpop: this.type = { if(wide) m.pop2 else m.pop; this }
  def if_==     : ThenDSL
  def if_!=     : ThenDSL
}

class RefTypedDSL(m: MethodDSL, val desc: ValDesc) extends TypedDSL(m) {
  def wide: Boolean = false

  def xload(v: VarIdx) : this.type = { m.aload(v); this }
  def xstore(v: VarIdx): this.type = { m.astore(v); this }
  def xaload           : this.type = { m.aaload; this }
  def xastore          : this.type = { m.aastore; this }
  def xreturn          : this.type = { m.areturn; this }
  def zero             : this.type = { m.aconst_null; this }
  def if_==            : ThenDSL = { m.aconst_null; new ThenDSL(IF_ACMPEQ, IF_ACMPNE, m, new Label) }
  def if_!=            : ThenDSL = { m.aconst_null; new ThenDSL(IF_ACMPNE, IF_ACMPEQ, m, new Label) }
}

abstract class NumericTypedDSL(m: MethodDSL) extends TypedDSL(m) {
  def desc: PrimitiveValDesc

  def xadd: this.type
  def xmul: this.type
  def xsub: this.type
  def xdiv: this.type
  def xneg: this.type
  def xrem: this.type
  def x2f: this.type
  def x2i: this.type
  def x2l: this.type
  def x2d: this.type

  protected[this] def xcmp: Unit
  protected[this] def if0(pos: Int, neg: Int): ThenDSL = {
    zero
    ifX(pos, neg)
  }
  protected[this] def ifX(pos: Int, neg: Int): ThenDSL = {
    xcmp
    new ThenDSL(pos, neg, m, new Label)
  }

  def if_==    : ThenDSL = if0(IF_ICMPEQ, IF_ICMPNE)
  def if_!=    : ThenDSL = if0(IF_ICMPNE, IF_ICMPEQ)
  def if_<     : ThenDSL = if0(IF_ICMPLT, IF_ICMPGE)
  def if_>     : ThenDSL = if0(IF_ICMPGT, IF_ICMPLE)
  def if_<=    : ThenDSL = if0(IF_ICMPLE, IF_ICMPGT)
  def if_>=    : ThenDSL = if0(IF_ICMPGE, IF_ICMPLT)

  def ifX_==    : ThenDSL = ifX(IF_ICMPEQ, IF_ICMPNE)
  def ifX_!=    : ThenDSL = ifX(IF_ICMPNE, IF_ICMPEQ)
  def ifX_<     : ThenDSL = ifX(IF_ICMPLT, IF_ICMPGE)
  def ifX_>     : ThenDSL = ifX(IF_ICMPGT, IF_ICMPLE)
  def ifX_<=    : ThenDSL = ifX(IF_ICMPLE, IF_ICMPGT)
  def ifX_>=    : ThenDSL = ifX(IF_ICMPGE, IF_ICMPLT)
}

class IntTypedDSL(m: MethodDSL) extends NumericTypedDSL(m) {
  protected[this] def xcmp: Unit = ()

  def desc: PrimitiveValDesc = Desc.I
  def wide: Boolean = false

  def xload(v: VarIdx) : this.type = { m.iload(v); this }
  def xstore(v: VarIdx): this.type = { m.istore(v); this }
  def xaload           : this.type = { m.iaload; this }
  def xastore          : this.type = { m.iastore; this }
  def xreturn          : this.type = { m.ireturn; this }
  def zero             : this.type = { m.iconst(0); this }
  def xadd             : this.type = { m.iadd; this }
  def xmul             : this.type = { m.imul; this }
  def xsub             : this.type = { m.isub; this }
  def xdiv             : this.type = { m.idiv; this }
  def xneg             : this.type = { m.ineg; this }
  def xrem             : this.type = { m.irem; this }
  def x2f              : this.type = { m.i2f; this }
  def x2i              : this.type = this
  def x2l              : this.type = { m.i2l; this }
  def x2d              : this.type = { m.l2d; this }

  override def if_==   : ThenDSL = new ThenDSL(IFEQ, IFNE, m, new Label)
  override def if_!=   : ThenDSL = new ThenDSL(IFNE, IFEQ, m, new Label)
  override def if_<    : ThenDSL = new ThenDSL(IFLT, IFGE, m, new Label)
  override def if_>    : ThenDSL = new ThenDSL(IFGT, IFLE, m, new Label)
  override def if_<=   : ThenDSL = new ThenDSL(IFLE, IFGT, m, new Label)
  override def if_>=   : ThenDSL = new ThenDSL(IFGE, IFLT, m, new Label)
}

class LongTypedDSL(m: MethodDSL) extends NumericTypedDSL(m) {
  protected[this] def xcmp: Unit = m.lcmp

  def desc: PrimitiveValDesc = Desc.J
  def wide: Boolean = true

  def xload(v: VarIdx) : this.type = { m.lload(v); this }
  def xstore(v: VarIdx): this.type = { m.lstore(v); this }
  def xaload           : this.type = { m.laload; this }
  def xastore          : this.type = { m.lastore; this }
  def xreturn          : this.type = { m.lreturn; this }
  def zero             : this.type = { m.lconst(0); this }
  def xadd             : this.type = { m.ladd; this }
  def xmul             : this.type = { m.lmul; this }
  def xsub             : this.type = { m.lsub; this }
  def xdiv             : this.type = { m.ldiv; this }
  def xneg             : this.type = { m.lneg; this }
  def xrem             : this.type = { m.lrem; this }
  def x2f              : this.type = { m.l2f; this }
  def x2i              : this.type = { m.l2i; this }
  def x2l              : this.type = this
  def x2d              : this.type = { m.l2d; this }
}

class FloatTypedDSL(m: MethodDSL) extends NumericTypedDSL(m) {
  protected[this] def xcmp: Unit = m.fcmpl

  def desc: PrimitiveValDesc = Desc.F
  def wide: Boolean = false

  def xload(v: VarIdx) : this.type = { m.fload(v); this }
  def xstore(v: VarIdx): this.type = { m.fstore(v); this }
  def xaload           : this.type = { m.faload; this }
  def xastore          : this.type = { m.fastore; this }
  def xreturn          : this.type = { m.freturn; this }
  def zero             : this.type = { m.fconst(0); this }
  def xadd             : this.type = { m.fadd; this }
  def xmul             : this.type = { m.fmul; this }
  def xsub             : this.type = { m.fsub; this }
  def xdiv             : this.type = { m.fdiv; this }
  def xneg             : this.type = { m.fneg; this }
  def xrem             : this.type = { m.frem; this }
  def x2f              : this.type = this
  def x2i              : this.type = { m.f2i; this }
  def x2l              : this.type = { m.f2l; this }
  def x2d              : this.type = { m.f2d; this }
}

class DoubleTypedDSL(m: MethodDSL) extends NumericTypedDSL(m) {
  protected[this] def xcmp: Unit = m.dcmpl

  def desc: PrimitiveValDesc = Desc.D
  def wide: Boolean = true

  def xload(v: VarIdx) : this.type = { m.dload(v); this }
  def xstore(v: VarIdx): this.type = { m.dstore(v); this }
  def xaload           : this.type = { m.daload; this }
  def xastore          : this.type = { m.dastore; this }
  def xreturn          : this.type = { m.dreturn; this }
  def zero             : this.type = { m.dconst(0); this }
  def xadd             : this.type = { m.dadd; this }
  def xmul             : this.type = { m.dmul; this }
  def xsub             : this.type = { m.dsub; this }
  def xdiv             : this.type = { m.ddiv; this }
  def xneg             : this.type = { m.dneg; this }
  def xrem             : this.type = { m.drem; this }
  def x2f              : this.type = { m.d2f; this }
  def x2i              : this.type = { m.d2i; this }
  def x2l              : this.type = { m.d2l; this }
  def x2d              : this.type = this
}
