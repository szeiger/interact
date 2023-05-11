package de.szeiger.interact.mt

object BitOps {
  @inline def byte0(i: Int): Int = (i & 0xFF).toByte
  @inline def byte1(i: Int): Int = ((i >>> 8) & 0xFF).toByte
  @inline def byte2(i: Int): Int = ((i >>> 16) & 0xFF).toByte
  @inline def byte3(i: Int): Int = ((i >>> 24) & 0xFF).toByte
  @inline def intOfBytes(b0: Int, b1: Int, b2: Int, b3: Int): Int = b0.toByte&0xFF | ((b1.toByte&0xFF) << 8) | ((b2.toByte&0xFF) << 16) | ((b3.toByte&0xFF) << 24)
  def checkedIntOfBytes(b0: Int, b1: Int, b2: Int, b3: Int): Int = {
    assert(b0 >= -128 && b0 <= 127)
    assert(b1 >= -128 && b1 <= 127)
    assert(b2 >= -128 && b2 <= 127)
    assert(b3 >= -128 && b3 <= 127)
    intOfBytes(b0, b1, b2, b3)
  }

  object IntOfBytes {
    @inline def unapply(i: Int): Some[(Int, Int, Int, Int)] = Some((byte0(i), byte1(i), byte2(i), byte3(i)))
  }

  @inline def short0(i: Int): Int = (i & 0xFFFF).toShort
  @inline def short1(i: Int): Int = ((i >>> 16) & 0xFFFF).toShort
  @inline def intOfShorts(s0: Int, s1: Int): Int = s0.toShort&0xFFFF | ((s1.toShort&0xFFFF) << 16)
  def checkedIntOfShorts(s0: Int, s1: Int): Int = {
    assert(s0 >= Short.MinValue && s0 <= Short.MaxValue)
    assert(s1 >= Short.MinValue && s1 <= Short.MaxValue)
    intOfShorts(s0, s1)
  }

  object IntOfShorts {
    @inline def unapply(i: Int): Some[(Int, Int)] = Some((short0(i), short1(i)))
  }
}
