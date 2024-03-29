package de.szeiger.interact.stc2

import de.szeiger.interact.ast.PayloadType
import de.szeiger.interact.codegen.{BoxDesc, BoxOps}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}

class PTOps(m: MethodDSL, pt: PayloadType, codeGen: CodeGen) extends BoxOps(m, PTOps.boxDesc(pt)) {
  import codeGen._

  def setCellPayload(ptw: VarIdx, arity: Int)(loadCell: => Unit)(loadUnboxedPayload: => Unit): this.type = {
    pt match {
      case PayloadType.LABEL =>
        loadCell
        m.lconst(Interpreter.payloadOffset(arity, pt)).ladd
        loadUnboxedPayload
        m.invokestatic(allocator_putLong)
      case PayloadType.INT =>
        loadCell
        m.lconst(Interpreter.payloadOffset(arity, pt)).ladd
        loadUnboxedPayload
        m.invokestatic(allocator_putInt)
      case PayloadType.REF =>
        m.aload(ptw)
        loadCell
        loadUnboxedPayload
        m.invoke(ptw_setProxy)
    }
    this
  }

  def getCellPayload(ptw: VarIdx, arity: Int)(loadCell: => Unit): this.type = {
    pt match {
      case PayloadType.REF =>
        m.aload(ptw)
        loadCell
        m.invoke(ptw_getProxy)
      case PayloadType.INT =>
        loadCell
        m.lconst(Interpreter.payloadOffset(arity, pt)).ladd
        m.invokestatic(allocator_getInt)
      case PayloadType.LABEL =>
        loadCell
        m.lconst(Interpreter.payloadOffset(arity, pt)).ladd
        m.invokestatic(allocator_getLong)
    }
    this
  }

  def extractUnboxed(loadValue: => Unit): this.type = {
    pt match {
      case PayloadType.INT =>
        loadValue
        m.iconst(32).lushr.l2i
    }
    this
  }

  def buildUnboxed(symId: Int)(loadValue: => Unit): this.type = {
    loadValue
    m.i2l.iconst(32).lshl
    m.lconst((symId.toLong << Interpreter.TAGWIDTH) | Interpreter.TAG_UNBOXED).lor
    this
  }
}

object PTOps {
  def boxDesc(pt: PayloadType): BoxDesc = pt match {
    case PayloadType.INT => BoxDesc.intDesc
    case PayloadType.REF => BoxDesc.refDesc
    case PayloadType.LABEL => BoxDesc.longDesc
  }
  def apply(m: MethodDSL, pt: PayloadType)(implicit codeGen: CodeGen): PTOps = new PTOps(m, pt, codeGen)
}
