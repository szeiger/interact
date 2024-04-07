package de.szeiger.interact.codegen

import de.szeiger.interact.{IntBox, IntBoxImpl, LongBox, LongBoxImpl, RefBox, RefBoxImpl}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}

class BoxDesc private (val boxT: InterfaceOwner, val implT: ClassOwner, val unboxedT: ValDesc) {
  lazy val newBox = implT.constr(tp.m().V)
  lazy val getValue = boxT.method("getValue", tp.m()(unboxedT))
  lazy val setValue = boxT.method("setValue", tp.m(unboxedT).V)

  def implementInterface(c: ClassDSL, owner: ClassOwner): Unit = {
    if(unboxedT != tp.V) {
      val field = owner.field("value", unboxedT)
      c.field(Acc.PUBLIC, field)
      c.setter(field)
      c.getter(field)
    }
  }
}

object BoxDesc {
  val intDesc = new BoxDesc(tp.i[IntBox], tp.c[IntBoxImpl], tp.I)
  val longDesc = new BoxDesc(tp.i[LongBox], tp.c[LongBoxImpl], tp.J)
  val refDesc = new BoxDesc(tp.i[RefBox], tp.c[RefBoxImpl], tp.Object)
  val voidDesc = new BoxDesc(null, null, tp.V)
}

class BoxOps(m: MethodDSL, val boxDesc: BoxDesc) {
  protected[this] lazy val t: TypedDSL = TypedDSL(boxDesc.unboxedT, m)

  def unboxedT: ValDesc = boxDesc.unboxedT

  def load(v: VarIdx) = t.xload(v)
  def store(v: VarIdx) = t.xstore(v)

  def unboxedClass: Class[_] = boxDesc.unboxedT.jvmClass.get
  def boxedClass: Class[_] = boxDesc.boxT.jvmClass.get

  def getBoxValue = m.invoke(boxDesc.getValue)
  def setBoxValue = m.invoke(boxDesc.setValue)
  def newBoxStore(name: String): VarIdx =  m.newInitDup(boxDesc.newBox)().storeLocal(boxDesc.implT, name)
  def newBoxStoreDup: VarIdx = m.newInitDup(boxDesc.newBox)().dup.storeLocal(boxDesc.implT)
}
