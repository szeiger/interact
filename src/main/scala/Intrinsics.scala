package de.szeiger.interact

object Intrinsics {
  def add(a: Int, b: Int, res: IntBox): Unit = res.setValue(a + b)
  def mult(a: Int, b: Int, res: IntBox): Unit = res.setValue(a * b)
  def strlen(s: String): Int = s.length

  def eraseRef(o: AnyRef): Unit = o match {
    case o: LifecycleManaged => o.erase()
    case _ =>
  }

  def dupRef(o: AnyRef, r1: RefBox, r2: RefBox): Unit = {
    r1.setValue(o)
    r2.setValue(o match {
      case o: LifecycleManaged => o.copy()
      case o => o
    })
  }

  def eq(a: Any, b: Any): Boolean = a == b
  def intAdd(a: Int, b: Int): Int = a + b
  def intSub(a: Int, b: Int): Int = a - b

  def createLabel(r: RefBox): Unit = r.setValue(new AnyRef)
}
