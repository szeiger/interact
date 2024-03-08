package de.szeiger.interact.stc2

import de.szeiger.interact.ast.PayloadType

object Allocator {
  val UNSAFE = {
    val f = classOf[sun.misc.Unsafe].getDeclaredField("theUnsafe")
    f.setAccessible(true)
    f.get(null).asInstanceOf[sun.misc.Unsafe]
  }
  val allocLength = 1024L * 1024L * 1024L

  def auxCPOffset(p: Int): Int = 8 + (p * 8)
  def payloadOffset(arity: Int): Int = 8 + (arity * 8)

  def cellSize(arity: Int, pt: PayloadType) = {
    val psize = pt match {
      case PayloadType.VOID => 0
      case PayloadType.INT => 8 // with padding
      case PayloadType.LABEL | PayloadType.REF => 8
    }
    arity*8 + 8 + psize
  }

  def symId(c: Long): Int = getInt(c) >> 1
  def auxCP(c: Long, p: Int): Long = getLong(c + auxCPOffset(p)) & -3L
  private[this] def setAuxCP(c: Long, p: Int, cp2: Long): Unit = putLong(c + auxCPOffset(p), cp2)
  def setAux(c: Long, p: Int, c2: Long, p2: Int): Unit = setAuxCP(c, p, encodeAux(c2, p2))

  private[this] def encodeAux(c: Long, p: Int) = {
    val l = c + auxCPOffset(p)
    if(p >= 0) l | 2L else l
  }

  def findCellAndPort(_cp: Long): (Long, Int) = {
    var cp = _cp
    if((cp & 1L) == 1L) {
      (cp, -1)
    } else {
      cp = cp & -3L
      var p = -1
      while((getInt(cp - auxCPOffset(p)) & 1) == 0)
        p += 1
      (cp - auxCPOffset(p), p)
    }
  }

  // used by code generator:
  def putInt(address: Long, value: Int): Unit = UNSAFE.putInt(address, value)
  def getInt(address: Long): Int = UNSAFE.getInt(address)
  def putLong(address: Long, value: Long): Unit = UNSAFE.putLong(address, value)
  def getLong(address: Long): Long = UNSAFE.getLong(address)
}

class Allocator {
  import Allocator._
  private[this] val block = UNSAFE.allocateMemory(allocLength)
  private[this] val end = block + allocLength
  private[this] var next = block

  def dispose(): Unit = UNSAFE.freeMemory(block)

  def alloc(len: Int): Long = {
    val o = next
    next += len
    assert(next < end)
    o
  }

  def free(address: Long, len: Int): Unit = {
    //TODO
  }

  def newCell(symId: Int, arity: Int, pt: PayloadType = PayloadType.VOID): Long = {
    val sz = cellSize(arity, pt)
    val o = alloc(sz)
    putInt(o, (symId << 1) | 1)
    o
  }

  def freeCell(address: Long, arity: Int, pt: PayloadType = PayloadType.VOID): Unit =
    free(address, cellSize(arity, pt))

  // 4 (symId << 1) | 1
  // 4 pad
  // 8 cp_0
  // ...
  // 8 cp_n
  // (0/4/8) payload
}
