package de.szeiger.interact.codegen.dsl

import org.objectweb.asm.Opcodes._

trait AccessFlags extends Any {
  protected[this] def acc: Int
  def PUBLIC       = new Acc(acc | ACC_PUBLIC)
  def PRIVATE      = new Acc(acc | ACC_PRIVATE)
  def PROTECTED    = new Acc(acc | ACC_PROTECTED)
  def STATIC       = new Acc(acc | ACC_STATIC)
  def FINAL        = new Acc(acc | ACC_FINAL)
  def SUPER        = new Acc(acc | ACC_SUPER)
  def SYNCHRONIZED = new Acc(acc | ACC_SYNCHRONIZED)
  def OPEN         = new Acc(acc | ACC_OPEN)
  def TRANSITIVE   = new Acc(acc | ACC_TRANSITIVE)
  def VOLATILE     = new Acc(acc | ACC_VOLATILE)
  def BRIDGE       = new Acc(acc | ACC_BRIDGE)
  def STATIC_PHASE = new Acc(acc | ACC_STATIC_PHASE)
  def VARARGS      = new Acc(acc | ACC_VARARGS)
  def TRANSIENT    = new Acc(acc | ACC_TRANSIENT)
  def NATIVE       = new Acc(acc | ACC_NATIVE)
  def INTERFACE    = new Acc(acc | ACC_INTERFACE)
  def ABSTRACT     = new Acc(acc | ACC_ABSTRACT)
  def STRICT       = new Acc(acc | ACC_STRICT)
  def SYNTHETIC    = new Acc(acc | ACC_SYNTHETIC)
  def ANNOTATION   = new Acc(acc | ACC_ANNOTATION)
  def ENUM         = new Acc(acc | ACC_ENUM)
  def MANDATED     = new Acc(acc | ACC_MANDATED)
  def MODULE       = new Acc(acc | ACC_MODULE)
  def RECORD       = new Acc(acc | ACC_RECORD)
  def DEPRECATED   = new Acc(acc | ACC_DEPRECATED)
}

final class Acc(val acc: Int) extends AnyVal with AccessFlags {
  def | (other: Acc): Acc = new Acc(acc | other.acc)
  def has (other: Acc): Boolean = (acc & other.acc) == other.acc
}

object Acc extends AccessFlags {
  protected[this] def acc = 0
  def none: Acc = new Acc(0)
}
