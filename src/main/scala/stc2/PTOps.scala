package de.szeiger.interact.stc2

import de.szeiger.interact.ast.PayloadType
import de.szeiger.interact.codegen.{BoxDesc, BoxOps}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import de.szeiger.interact.offheap.Allocator

class PTOps(m: MethodDSL, pt: PayloadType, codeGen: CodeGen) extends BoxOps(m, PTOps.boxDesc(pt)) {
  import codeGen._

  def setCellPayload(ptw: VarIdx, arity: Int)(loadCell: => Unit)(loadUnboxedPayload: => Unit): this.type = {
    pt match {
      case PayloadType.LABEL =>
        loadCell
        m.lconst(Allocator.payloadOffset(arity, pt)).ladd
        loadUnboxedPayload
        m.invokestatic(allocator_putLong)
      case PayloadType.INT =>
        loadCell
        m.lconst(Allocator.payloadOffset(arity, pt)).ladd
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
        m.lconst(Allocator.payloadOffset(arity, pt)).ladd
        m.invokestatic(allocator_getInt)
      case PayloadType.LABEL =>
        loadCell
        m.lconst(Allocator.payloadOffset(arity, pt)).ladd
        m.invokestatic(allocator_getLong)
    }
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
