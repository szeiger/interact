package de.szeiger.interact.stc2

import de.szeiger.interact.{IntBox, IntBoxImpl, LongBox, LongBoxImpl, RefBox, RefBoxImpl}
import de.szeiger.interact.ast.PayloadType
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import de.szeiger.interact.offheap.Allocator

class PTOps(m: MethodDSL, pt: PayloadType, codeGen: CodeGen) {
  import codeGen._

  val intBoxT = tp.i[IntBox]
  val longBoxT = tp.i[LongBox]
  val refBoxT = tp.i[RefBox]
  val intBoxImplT = tp.c[IntBoxImpl]
  val refBoxImplT = tp.c[RefBoxImpl]
  val longBoxImplT = tp.c[LongBoxImpl]
  val new_IntBoxImpl = intBoxImplT.constr(tp.m().V)
  val new_RefBoxImpl = refBoxImplT.constr(tp.m().V)
  val new_LongBoxImpl = longBoxImplT.constr(tp.m().V)
  val intBox_getValue = intBoxT.method("getValue", tp.m().I)
  val longBox_getValue = longBoxT.method("getValue", tp.m().J)
  val refBox_getValue = refBoxT.method("getValue", tp.m()(tp.c[AnyRef]))

  def load(v: VarIdx): this.type = {
    pt match {
      case PayloadType.INT => m.iload(v)
      case PayloadType.REF => m.aload(v)
      case PayloadType.LABEL => m.lload(v)
    }
    this
  }

  def store(v: VarIdx): this.type = {
    pt match {
      case PayloadType.INT => m.istore(v)
      case PayloadType.REF => m.astore(v)
      case PayloadType.LABEL => m.lstore(v)
    }
    this
  }

  def newBoxStore(name: String): VarIdx = pt match {
    case PayloadType.INT => m.newInitDup(new_IntBoxImpl)().storeLocal(intBoxImplT, name)
    case PayloadType.REF => m.newInitDup(new_RefBoxImpl)().storeLocal(refBoxImplT, name)
    case PayloadType.LABEL => m.newInitDup(new_LongBoxImpl)().storeLocal(longBoxImplT, name)
  }

  def newBoxStoreDup: VarIdx = pt match {
    case PayloadType.INT => m.newInitDup(new_IntBoxImpl)().dup.storeLocal(intBoxImplT)
    case PayloadType.REF => m.newInitDup(new_RefBoxImpl)().dup.storeLocal(refBoxImplT)
    case PayloadType.LABEL => m.newInitDup(new_LongBoxImpl)().dup.storeLocal(longBoxImplT)
  }

  def getBoxValue: this.type = {
    pt match {
      case PayloadType.INT => m.invoke(intBox_getValue)
      case PayloadType.REF => m.invoke(refBox_getValue)
      case PayloadType.LABEL => m.invoke(longBox_getValue)
    }
    this
  }

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

  def unboxedDesc: ValDesc = pt match {
    case PayloadType.INT => tp.I
    case PayloadType.REF => tp.Object
    case PayloadType.LABEL => tp.J
  }

  def unboxedClass: Class[_] = pt match {
    case PayloadType.INT => classOf[Int]
    case PayloadType.REF => classOf[AnyRef]
    case PayloadType.LABEL => classOf[Long]
  }
}

object PTOps {
  def apply(m: MethodDSL, pt: PayloadType)(implicit codeGen: CodeGen): PTOps = new PTOps(m, pt, codeGen)
}
