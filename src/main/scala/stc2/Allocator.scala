package de.szeiger.interact.stc2

import de.szeiger.interact.ast.PayloadType

object Allocator {
  val UNSAFE = {
    val f = classOf[sun.misc.Unsafe].getDeclaredField("theUnsafe")
    f.setAccessible(true)
    f.get(null).asInstanceOf[sun.misc.Unsafe]
  }
  val allocLength = 1024L * 1024L * 1024L

  def arityOffset: Int = 4
  def auxCellOffset(p: Int): Int = 8 + (p * 16)
  def auxPortOffset(p: Int): Int = 16 + (p * 16)
  def payloadOffset(arity: Int): Int = 8 + (arity * 16)

  def cellSize(arity: Int, pt: PayloadType) = {
    val psize = pt match {
      case PayloadType.VOID => 0
      case PayloadType.INT => 8 // with padding
      case PayloadType.LABEL | PayloadType.REF => 8
    }
    arity*16 + 8 + psize
  }

  def symId(c: Long): Int = getInt(c) >> 1
  def auxCell(c: Long, p: Int): Long = getLong(c + auxCellOffset(p))
  def auxPort(c: Long, p: Int): Int = getInt(c + auxPortOffset(p))
  def setAux(c: Long, p: Int, c2: Long, p2: Int): Unit ={
    setLong(c + auxCellOffset(p), c2)
    setInt(c + auxPortOffset(p), p2)
  }

  // used by code generator:
  def setInt(address: Long, value: Int): Unit = UNSAFE.putInt(address, value)
  def getInt(address: Long): Int = UNSAFE.getInt(address)
  def setLong(address: Long, value: Long): Unit = UNSAFE.putLong(address, value)
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
    UNSAFE.setMemory(o, sz, 0)
    setInt(o, (symId << 1) | 1)
    o
  }

  def freeCell(address: Long, arity: Int, pt: PayloadType = PayloadType.VOID): Unit =
    free(address, cellSize(arity, pt))

  // 4 (symId << 1) | 1
  // 4 pad
  // 8 c0
  // 4 p0
  // 4 pad
  // ...
  // 8 cn
  // 4 pn
  // 4 pad
  // (0/4/8) payload
}
