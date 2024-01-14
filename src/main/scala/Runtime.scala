package de.szeiger.interact

trait IntOutput { def setValue(i: Int): Unit }
trait IntBox extends IntOutput { def getValue: Int }
trait RefOutput { def setValue(o: AnyRef): Unit }
trait RefBox extends RefOutput { def getValue: AnyRef } // Also used for Label
trait LifecycleManaged { def erase(): Unit; def copy(): LifecycleManaged }

object Runtime {
  def add(a: Int, b: Int, res: IntOutput): Unit = res.setValue(a + b)
  def mult(a: Int, b: Int, res: IntOutput): Unit = res.setValue(a * b)
  def strlen(s: String): Int = s.length

  def eraseRef(o: AnyRef): Unit = o match {
    case o: LifecycleManaged => o.erase()
    case _ =>
  }

  def dupRef(o: AnyRef, r1: RefOutput, r2: RefOutput): Unit = {
    r1.setValue(o)
    r2.setValue(o match {
      case o: LifecycleManaged => o.copy()
      case o => o
    })
  }

  def eq(a: AnyRef, b: AnyRef): Boolean = a == b
  def eq(a: Int, b: Int): Boolean = a == b
  def intAdd(a: Int, b: Int): Int = a + b
  def intSub(a: Int, b: Int): Int = a - b
  def intMult(a: Int, b: Int): Int = a * b
}
