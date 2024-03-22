package de.szeiger.interact.codegen

import de.szeiger.interact.{IntBox, IntBoxImpl, LongBox, LongBoxImpl, RefBox, RefBoxImpl}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}

class BoxDesc(val boxT: InterfaceOwner, val implT: ClassOwner, val unboxedT: ValDesc) {
  val newBox = implT.constr(tp.m().V)
  val getValue = boxT.method("getValue", tp.m()(unboxedT))
  val setValue = boxT.method("setValue", tp.m(unboxedT).V)

  def implementInterface(c: ClassDSL, owner: ClassOwner): Unit = {
    val field = owner.field("value", unboxedT)
    c.field(Acc.PUBLIC, field)
    c.setter(field)
    c.getter(field)
  }
}

object BoxDesc {
  val intDesc = new BoxDesc(tp.i[IntBox], tp.c[IntBoxImpl], tp.I)
  val longDesc = new BoxDesc(tp.i[LongBox], tp.c[LongBoxImpl], tp.J)
  val refDesc = new BoxDesc(tp.i[RefBox], tp.c[RefBoxImpl], tp.Object)
}

class BoxOps(m: MethodDSL, val desc: BoxDesc) {
  protected[this] val t: TypedDSL = TypedDSL(desc.unboxedT, m)

  def load(v: VarIdx) = t.xload(v)
  def store(v: VarIdx) = t.xstore(v)

  def unboxedClass: Class[_] = desc.unboxedT.jvmClass.get
  def boxedClass: Class[_] = desc.boxT.jvmClass.get

  def getBoxValue = m.invoke(desc.getValue)
  def setBoxValue = m.invoke(desc.setValue)
  def newBoxStore(name: String): VarIdx =  m.newInitDup(desc.newBox)().storeLocal(desc.implT, name)
  def newBoxStoreDup: VarIdx = m.newInitDup(desc.newBox)().dup.storeLocal(desc.implT)
}
