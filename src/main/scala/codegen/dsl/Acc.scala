package de.szeiger.interact.codegen.dsl

import org.objectweb.asm.Opcodes._

trait AccessFlags extends Any {
  protected[this] def acc: Int
  @inline def PUBLIC       = new Acc(acc | ACC_PUBLIC)
  @inline def PRIVATE      = new Acc(acc | ACC_PRIVATE)
  @inline def PROTECTED    = new Acc(acc | ACC_PROTECTED)
  @inline def STATIC       = new Acc(acc | ACC_STATIC)
  @inline def FINAL        = new Acc(acc | ACC_FINAL)
  @inline def SUPER        = new Acc(acc | ACC_SUPER)
  @inline def SYNCHRONIZED = new Acc(acc | ACC_SYNCHRONIZED)
  @inline def OPEN         = new Acc(acc | ACC_OPEN)
  @inline def TRANSITIVE   = new Acc(acc | ACC_TRANSITIVE)
  @inline def VOLATILE     = new Acc(acc | ACC_VOLATILE)
  @inline def BRIDGE       = new Acc(acc | ACC_BRIDGE)
  @inline def STATIC_PHASE = new Acc(acc | ACC_STATIC_PHASE)
  @inline def VARARGS      = new Acc(acc | ACC_VARARGS)
  @inline def TRANSIENT    = new Acc(acc | ACC_TRANSIENT)
  @inline def NATIVE       = new Acc(acc | ACC_NATIVE)
  @inline def INTERFACE    = new Acc(acc | ACC_INTERFACE)
  @inline def ABSTRACT     = new Acc(acc | ACC_ABSTRACT)
  @inline def STRICT       = new Acc(acc | ACC_STRICT)
  @inline def SYNTHETIC    = new Acc(acc | ACC_SYNTHETIC)
  @inline def ANNOTATION   = new Acc(acc | ACC_ANNOTATION)
  @inline def ENUM         = new Acc(acc | ACC_ENUM)
  @inline def MANDATED     = new Acc(acc | ACC_MANDATED)
  @inline def MODULE       = new Acc(acc | ACC_MODULE)
  @inline def RECORD       = new Acc(acc | ACC_RECORD)
  @inline def DEPRECATED   = new Acc(acc | ACC_DEPRECATED)
}

final class Acc(val acc: Int) extends AnyVal with AccessFlags {
  def | (other: Acc): Acc = new Acc(acc | other.acc)
  def has (other: Acc): Boolean = (acc & other.acc) == other.acc
}

object Acc extends AccessFlags {
  protected[this] final val acc = 0
  @inline def none: Acc = new Acc(0)
}
