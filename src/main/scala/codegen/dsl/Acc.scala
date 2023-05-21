package de.szeiger.interact.codegen.dsl

import org.objectweb.asm.Opcodes._

final class Acc(val acc: Int) extends AnyVal {
  def | (other: Acc): Acc = new Acc(acc | other.acc)
  def has (other: Acc): Boolean = (acc & other.acc) == other.acc
}

object Acc {
  val none         = new Acc(0)
  val PUBLIC       = new Acc(ACC_PUBLIC)
  val PRIVATE      = new Acc(ACC_PRIVATE)
  val PROTECTED    = new Acc(ACC_PROTECTED)
  val STATIC       = new Acc(ACC_STATIC)
  val FINAL        = new Acc(ACC_FINAL)
  val SUPER        = new Acc(ACC_SUPER)
  val SYNCHRONIZED = new Acc(ACC_SYNCHRONIZED)
  val OPEN         = new Acc(ACC_OPEN)
  val TRANSITIVE   = new Acc(ACC_TRANSITIVE)
  val VOLATILE     = new Acc(ACC_VOLATILE)
  val BRIDGE       = new Acc(ACC_BRIDGE)
  val STATIC_PHASE = new Acc(ACC_STATIC_PHASE)
  val VARARGS      = new Acc(ACC_VARARGS)
  val TRANSIENT    = new Acc(ACC_TRANSIENT)
  val NATIVE       = new Acc(ACC_NATIVE)
  val INTERFACE    = new Acc(ACC_INTERFACE)
  val ABSTRACT     = new Acc(ACC_ABSTRACT)
  val STRICT       = new Acc(ACC_STRICT)
  val SYNTHETIC    = new Acc(ACC_SYNTHETIC)
  val ANNOTATION   = new Acc(ACC_ANNOTATION)
  val ENUM         = new Acc(ACC_ENUM)
  val MANDATED     = new Acc(ACC_MANDATED)
  val MODULE       = new Acc(ACC_MODULE)
  val RECORD       = new Acc(ACC_RECORD)
  val DEPRECATED   = new Acc(ACC_DEPRECATED)
}
