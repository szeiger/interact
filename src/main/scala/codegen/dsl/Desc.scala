package de.szeiger.interact.codegen.dsl

import org.objectweb.asm.Type

import scala.reflect.ClassTag

abstract class Desc {
  def desc: String
  def isArray: Boolean = desc.startsWith("[")
  def isMethod: Boolean = desc.startsWith("(")
  def isClass: Boolean = desc.startsWith("L")
  override def hashCode() = desc.hashCode
  override def equals(obj: Any) = obj match {
    case o: Desc => desc == o.desc
    case _ => false
  }
}
abstract class MethodDesc extends Desc
abstract class ValDesc extends Desc {
  def a: ValDesc = new Desc.ValDescImpl("["+desc, jvmClass.map(c => c.arrayType()))
  def width: Int = {
    val d = desc
    if(d == "J" || d == "D") 2
    else 1
  }
  def jvmClass: Option[Class[_]]
}
final class PrimitiveValDesc(val desc: String, val jvmType: Class[_]) extends ValDesc {
  def jvmClass = Some(jvmType)
}

object Desc {
  import java.lang.{String => JString}
  private[dsl] class ValDescImpl(val desc: JString, val jvmClass: Option[Class[_]]) extends ValDesc
  private[this] class MethodDescImpl(val desc: JString) extends MethodDesc
  class MethodArgs private[Desc] (params: Seq[ValDesc]) {
    private[this] def d = params.iterator.map(_.desc).mkString("(", "", ")")
    def B: MethodDesc = new MethodDescImpl(s"${d}B")
    def Z: MethodDesc = new MethodDescImpl(s"${d}Z")
    def C: MethodDesc = new MethodDescImpl(s"${d}C")
    def I: MethodDesc = new MethodDescImpl(s"${d}I")
    def S: MethodDesc = new MethodDescImpl(s"${d}S")
    def D: MethodDesc = new MethodDescImpl(s"${d}D")
    def F: MethodDesc = new MethodDescImpl(s"${d}F")
    def J: MethodDesc = new MethodDescImpl(s"${d}J")
    def V: MethodDesc = new MethodDescImpl(s"${d}V")
    def apply(ret: ValDesc): MethodDesc = new MethodDescImpl(s"${d}${ret.desc}")
  }
  val B: PrimitiveValDesc = new PrimitiveValDesc("B", java.lang.Byte.TYPE)
  val Z: PrimitiveValDesc = new PrimitiveValDesc("Z", java.lang.Boolean.TYPE)
  val C: PrimitiveValDesc = new PrimitiveValDesc("C", java.lang.Character.TYPE)
  val I: PrimitiveValDesc = new PrimitiveValDesc("I", java.lang.Integer.TYPE)
  val S: PrimitiveValDesc = new PrimitiveValDesc("S", java.lang.Short.TYPE)
  val D: PrimitiveValDesc = new PrimitiveValDesc("D", java.lang.Double.TYPE)
  val F: PrimitiveValDesc = new PrimitiveValDesc("F", java.lang.Float.TYPE)
  val J: PrimitiveValDesc = new PrimitiveValDesc("J", java.lang.Long.TYPE)
  val V: PrimitiveValDesc = new PrimitiveValDesc("V", java.lang.Void.TYPE)
  val Object: ClassOwner = c[AnyRef]
  val String: ClassOwner = c[String]
  def m(desc: JString): MethodDesc = new MethodDescImpl(desc)
  def m(jMethod: java.lang.reflect.Method): MethodDesc = m(Type.getMethodDescriptor(jMethod))
  def m(params: ValDesc*): MethodArgs = new MethodArgs(params)
  def c(className: JString): ClassOwner = new ClassOwner(className, None)
  def c(cls: Class[_]): ClassOwner = ClassOwner(cls)
  def c[T : ClassTag]: ClassOwner = ClassOwner.apply[T]
  def i(className: JString): InterfaceOwner = new InterfaceOwner(className, None)
  def i(cls: Class[_]): InterfaceOwner = InterfaceOwner(cls)
  def i[T : ClassTag]: InterfaceOwner = InterfaceOwner.apply[T]
  def o(cls: Class[_]): Owner = Owner(cls)
  def o[T : ClassTag]: Owner = Owner.apply[T]
}

sealed abstract class Owner extends ValDesc {
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
class ClassOwner(val className: String, val jvmClass: Option[Class[_]]) extends Owner {
  def javaName = className.replace('/', '.')
  def isInterface = false
  def constr(desc: MethodDesc): ConstructorRef = new ConstructorRef(this, desc)
}
object ClassOwner {
  def apply[T](implicit ct: ClassTag[T]): ClassOwner = apply(ct.runtimeClass)
  def apply(cls: Class[_]): ClassOwner = {
    assert(!cls.isInterface)
    new ClassOwner(cls.getName.replace('.', '/'), Some(cls))
  }
}
class InterfaceOwner(val className: String, val jvmClass: Option[Class[_]]) extends Owner {
  def isInterface = true
}
object InterfaceOwner {
  def apply[T](implicit ct: ClassTag[T]): InterfaceOwner = apply(ct.runtimeClass)
  def apply(cls: Class[_]): InterfaceOwner = {
    assert(cls.isInterface)
    new InterfaceOwner(cls.getName.replace('.', '/'), Some(cls))
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
