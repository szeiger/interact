package de.szeiger.interact.codegen.dsl

import org.objectweb.asm.Type

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
  def m(desc: String): MethodDesc = new MethodDescImpl(desc)
  def m(jMethod: java.lang.reflect.Method): MethodDesc = m(Type.getMethodDescriptor(jMethod))
  def m(params: ValDesc*): MethodArgs = new MethodArgs(params)
  def c(className: String): ClassOwner = new ClassOwner(className)
  def c(cls: Class[_]): ClassOwner = ClassOwner(cls)
  def c[T : ClassTag]: ClassOwner = ClassOwner.apply[T]
  def i(className: String): InterfaceOwner = new InterfaceOwner(className)
  def i(cls: Class[_]): InterfaceOwner = InterfaceOwner(cls)
  def i[T : ClassTag]: InterfaceOwner = InterfaceOwner.apply[T]
  def o(cls: Class[_]): Owner = Owner(cls)
  def o[T : ClassTag]: Owner = Owner.apply[T]
}

sealed trait Owner extends ValDesc {
  def className: String
  def isInterface: Boolean
  final override def toString: String = className
  def desc: String = s"L$className;"

  def method(name: String, desc: MethodDesc): MethodRef = new MethodRef(this, name, desc)
  def field(name: String, desc: ValDesc): FieldRef = new FieldRef(this, name, desc)
}
object Owner {
  def apply[T](implicit ct: ClassTag[T]): Owner = apply(ct.runtimeClass)
  def apply(cls: Class[_]): Owner =
    if(cls.isInterface) InterfaceOwner(cls) else ClassOwner(cls)
}
class ClassOwner(val className: String) extends Owner {
  def isInterface = false
  def constr(desc: MethodDesc): ConstructorRef = new ConstructorRef(this, desc)
}
object ClassOwner {
  def apply[T](implicit ct: ClassTag[T]): ClassOwner = apply(ct.runtimeClass)
  def apply(cls: Class[_]): ClassOwner = {
    assert(!cls.isInterface)
    new ClassOwner(cls.getName.replace('.', '/'))
  }
}
class InterfaceOwner(val className: String) extends Owner {
  def isInterface = true
}
object InterfaceOwner {
  def apply[T](implicit ct: ClassTag[T]): InterfaceOwner = apply(ct.runtimeClass)
  def apply(cls: Class[_]): InterfaceOwner = {
    assert(cls.isInterface)
    new InterfaceOwner(cls.getName.replace('.', '/'))
  }
}

case class MethodRef(owner: Owner, name: String, desc: MethodDesc) {
  def on(owner: Owner): MethodRef = new MethodRef(owner, name, desc)
}
object MethodRef {
  def apply(jMethod: java.lang.reflect.Method): MethodRef =
    Desc.o(jMethod.getDeclaringClass).method(jMethod.getName, Desc.m(jMethod))
}

case class ConstructorRef(tpe: ClassOwner, desc: MethodDesc)

case class FieldRef(owner: Owner, name: String, desc: ValDesc)
