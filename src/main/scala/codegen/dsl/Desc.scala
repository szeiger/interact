package de.szeiger.interact.codegen.dsl

import scala.reflect.ClassTag

trait Desc { def desc: String }
trait MethodDesc extends Desc
trait ValDesc extends Desc {
  def a: ValDesc = new Desc.ValDescImpl("["+desc)
}

object Desc {
  private[dsl] class ValDescImpl(val desc: String) extends ValDesc
  private[this] class MethodDescImpl(val desc: String) extends MethodDesc
  class MethodArgs private[Desc] (params: Seq[ValDesc]) {
    private[this] def d = params.iterator.map(_.desc).mkString("(", "", ")")
    def I: MethodDesc = new MethodDescImpl(s"${d}I")
    def V: MethodDesc = new MethodDescImpl(s"${d}V")
    def apply(ret: ValDesc): MethodDesc = new MethodDescImpl(s"${d}${ret.desc}")
  }
  val I: ValDesc = new ValDescImpl("I")
  def m(params: ValDesc*): MethodArgs = new MethodArgs(params)
  def c(className: String) = new ClassOwner(className)
  def c[T : ClassTag] = ClassOwner.apply[T]
  def i(className: String) = new InterfaceOwner(className)
  def i[T : ClassTag] = InterfaceOwner.apply[T]
}

sealed trait Owner extends ValDesc {
  def className: String
  def isInterface: Boolean
  final override def toString: String = className
  def desc: String = s"L$className;"

  def method(name: String, desc: MethodDesc): MethodRef = new MethodRef(this, name, desc)
  def constr(desc: MethodDesc): ConstructorRef = new ConstructorRef(this, desc)
  def field(name: String, desc: ValDesc): FieldRef = new FieldRef(this, name, desc)
}
class ClassOwner(val className: String) extends Owner {
  def isInterface = false
}
object ClassOwner {
  def apply[T](implicit ct: ClassTag[T]) = {
    assert(!ct.runtimeClass.isInterface)
    new ClassOwner(ct.runtimeClass.getName.replace('.', '/'))
  }
}
class InterfaceOwner(val className: String) extends Owner {
  def isInterface = true
}
object InterfaceOwner {
  def apply[T](implicit ct: ClassTag[T]) = {
    assert(ct.runtimeClass.isInterface)
    new InterfaceOwner(ct.runtimeClass.getName.replace('.', '/'))
  }
}

case class MethodRef(owner: Owner, name: String, desc: MethodDesc)

case class ConstructorRef(tpe: Owner, desc: MethodDesc)

case class FieldRef(owner: Owner, name: String, desc: ValDesc)
