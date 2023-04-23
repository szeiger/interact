package de.szeiger.interact.mt

import org.junit.Assert._
import org.junit.Test

import BitOps._

class BitOpsTest {

  val vals = Seq(-128, -127, -1, 0, 1, 126, 127)

  @Test
  def testByte0(): Unit = {
    for {
      v0 <- vals
    } {
      val i = checkedIntOfBytes(v0, 0, 0, 0)
      assertEquals(v0, byte0(i))
    }
  }

  @Test
  def testByte1(): Unit = {
    for {
      v1 <- vals
    } {
      val i = checkedIntOfBytes(0, v1, 0, 0)
      assertEquals(v1, byte1(i))
    }
  }

  @Test
  def testByte2(): Unit = {
    for {
      v2 <- vals
    } {
      val i = checkedIntOfBytes(0, 0, v2, 0)
      assertEquals(v2, byte2(i))
    }
  }

  @Test
  def testByte3(): Unit = {
    for {
      v3 <- vals
    } {
      val i = checkedIntOfBytes(0, 0, 0, v3)
      assertEquals(v3, byte3(i))
    }
  }

  @Test
  def testMixed(): Unit = {
    val vals = Seq(-128, -127, -1, 0, 1, 126, 127)
    for {
      v0 <- vals
      v1 <- vals
      v2 <- vals
      v3 <- vals
    } {
      val i = checkedIntOfBytes(v0, v1, v2, v3)
      assertEquals(v0, byte0(i))
      assertEquals(v1, byte1(i))
      assertEquals(v2, byte2(i))
      assertEquals(v3, byte3(i))
    }
  }
}
