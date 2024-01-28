package de.szeiger.interact

trait IntOutput { def setValue(i: Int): Unit }
trait IntBox extends IntOutput { def getValue: Int }
trait RefOutput { def setValue(o: AnyRef): Unit }
trait RefBox extends RefOutput { def getValue: AnyRef } // Also used for Label
trait LifecycleManaged { def erase(): Unit; def copy(): LifecycleManaged }

// Standalone boxes used for boxed temporary values in inlined payload computations
final class IntBoxImpl extends IntBox {
  private[this] var value: Int = _
  def getValue: Int = value
  def setValue(v: Int): Unit = value = v
}
final class RefBoxImpl extends RefBox {
  private[this] var value: AnyRef = _
  def getValue: AnyRef = value
  def setValue(v: AnyRef): Unit = value = v
}

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
  def eqLabel(a: AnyRef, b: AnyRef): Boolean = a eq b
  def eq(a: Int, b: Int): Boolean = a == b
  def intAdd(a: Int, b: Int): Int = a + b
  def intSub(a: Int, b: Int): Int = a - b
  def intMult(a: Int, b: Int): Int = a * b
}
