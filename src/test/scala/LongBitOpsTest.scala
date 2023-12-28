package de.szeiger.interact

import org.junit.Assert._
import org.junit.Test

import LongBitOps._

class LongBitOpsTest {

  val vals = Seq(Short.MinValue, Short.MinValue+1, -128, -127, -1, 0, 1, 126, 127, Short.MaxValue-1, Short.MaxValue)

  @Test
  def testShort0(): Unit = {
    for {
      v0 <- vals
    } {
      val i = checkedLongOfShorts(v0, 0, 0, 0)
      assertEquals(v0, short0(i))
    }
  }

  @Test
  def testShort1(): Unit = {
    for {
      v1 <- vals
    } {
      val i = checkedLongOfShorts(0, v1, 0, 0)
      assertEquals(v1, short1(i))
    }
  }

  @Test
  def testShort2(): Unit = {
    for {
      v2 <- vals
    } {
      val i = checkedLongOfShorts(0, 0, v2, 0)
      assertEquals(v2, short2(i))
    }
  }

  @Test
  def testShort3(): Unit = {
    for {
      v3 <- vals
    } {
      val i = checkedLongOfShorts(0, 0, 0, v3)
      assertEquals(v3, short3(i))
    }
  }

  @Test
  def testMixed(): Unit = {
    for {
      v0 <- vals
      v1 <- vals
      v2 <- vals
      v3 <- vals
    } {
      val i = checkedLongOfShorts(v0, v1, v2, v3)
      assertEquals(v0, short0(i))
      assertEquals(v1, short1(i))
      assertEquals(v2, short2(i))
      assertEquals(v3, short3(i))
    }
  }
}
