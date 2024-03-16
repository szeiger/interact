package de.szeiger.interact.offheap

import de.szeiger.interact.ast.PayloadType

import scala.collection.mutable.ArrayBuffer

object Allocator {
  // 4 (symId << 1) | 1
  // 4 payload (int, ref proxy)
  // 8 cp_0
  // ...
  // 8 cp_n
  // (0/8) payload (label)

  val UNSAFE = {
    val f = classOf[sun.misc.Unsafe].getDeclaredField("theUnsafe")
    f.setAccessible(true)
    f.get(null).asInstanceOf[sun.misc.Unsafe]
  }

  def auxCPOffset(p: Int): Int = 8 + (p * 8)
  def payloadOffset(arity: Int, pt: PayloadType): Int =
    if(pt == PayloadType.LABEL) 8 + (arity * 8) else 4

  def cellSize(arity: Int, pt: PayloadType) = {
    val psize = if(pt == PayloadType.LABEL) 8 else 0
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

abstract class Allocator {
  import Allocator._

  def dispose(): Unit
  def alloc(len: Long): Long
  def free(address: Long, len: Long): Unit

  final def newCell(symId: Int, arity: Int, pt: PayloadType = PayloadType.VOID): Long = {
    val o = alloc(cellSize(arity, pt))
    putInt(o, (symId << 1) | 1)
    o
  }

  final def freeCell(address: Long, arity: Int, pt: PayloadType = PayloadType.VOID): Unit =
    free(address, cellSize(arity, pt))
}

abstract class ProxyAllocator extends Allocator {
  def allocProxied(len: Long): Long
  def freeProxied(o: Long, len: Long): Unit
  def getProxy(o: Long, len: Int): AnyRef
  def setProxy(o: Long, len: Int, v: AnyRef): Unit
}

object SystemAllocator extends Allocator {
  import Allocator._

  def dispose(): Unit = ()
  def alloc(len: Long): Long = UNSAFE.allocateMemory(len)
  def free(address: Long, len: Long): Unit = UNSAFE.freeMemory(address)
}

final class ArenaAllocator(blockSize: Long = 1024L*1024L*8L) extends Allocator {
  import Allocator._
  private[this] var block, end, next = 0L

  def dispose(): Unit = {
    while(block != 0L) {
      val n = UNSAFE.getLong(block)
      UNSAFE.freeMemory(block)
      block = n
    }
  }

  def alloc(len: Long): Long = {
    if(next + len >= end) {
      allocBlock()
      assert(next + len < end)
    }
    val o = next
    next += len
    o
  }

  def free(address: Long, len: Long): Unit = ()

  private[this] def allocBlock(): Unit = {
    val b = UNSAFE.allocateMemory(blockSize)
    UNSAFE.putLong(b, block)
    block = b
    next = b + 8
    end = b + blockSize
  }
}

final class SliceAllocator(blockSize: Long = 1024L*64L, maxSliceSize: Int = 256, arenaSize: Long = 1024L*1024L*8L) extends ProxyAllocator {
  assert(blockSize % 8 == 0)
  assert(maxSliceSize % 8 == 0)
  assert(blockSize >= maxSliceSize)

  private[this] val blockAllocator = new ArenaAllocator(arenaSize)
  private[this] val slices: Array[Slice] = Array.tabulate(maxSliceSize >> 3)(i => new Slice((i+1) << 3, blockSize, blockAllocator))
  private[this] val proxySlices: Array[ProxySlice] = Array.tabulate(maxSliceSize >> 3)(i => new ProxySlice((i+1) << 3, blockSize, blockAllocator))

  def dispose(): Unit = blockAllocator.dispose()
  def alloc(len: Long): Long = slices((len >> 3).toInt).alloc()
  def free(o: Long, len: Long): Unit = slices((len >> 3).toInt).free(o)
  def allocProxied(len: Long): Long = proxySlices((len >> 3).toInt).alloc()
  def freeProxied(o: Long, len: Long): Unit = proxySlices((len >> 3).toInt).free(o)

  def getProxy(o: Long, len: Int): AnyRef = proxySlices(len >> 3).getProxy(o)
  def setProxy(o: Long, len: Int, v: AnyRef): Unit = proxySlices(len >> 3).setProxy(o, v)
}

final class Slice(sliceSize: Int, blockSize: Long, parent: Allocator) {
  import Allocator._

  private[this] val allocSize = ((blockSize / sliceSize) * sliceSize) + 8
  private[this] var block, last, next, freeSlice = 0L

  private[this] def allocBlock(): Unit = {
    val b = parent.alloc(allocSize)
    UNSAFE.putLong(b, block)
    block = b
    next = b + 8
    last = b + allocSize - sliceSize
  }

  def alloc(): Long = {
    if(freeSlice != 0L) {
      val o = freeSlice
      freeSlice = UNSAFE.getLong(o)
      o
    } else {
      if(next >= last) allocBlock()
      val o = next
      next += sliceSize
      o
    }
  }

  def free(o: Long): Unit = {
    UNSAFE.putLong(o, freeSlice)
    freeSlice = o
  }
}

final class ProxySlice(_sliceSize: Int, _blockSize: Long, parent: Allocator) {
  import Allocator._

  private[this] val sliceAllocSize = _sliceSize + 8
  private[this] val numBlocks = (_blockSize / sliceAllocSize).toInt
  private[this] val allocSize = (numBlocks * sliceAllocSize) + 8
  private[this] var block, last, next, freeSlice = 0L
  private[this] val proxies: ArrayBuffer[Array[AnyRef]] = ArrayBuffer.empty

  @inline private[this] def coordsOf(o: Long) = {
    val l = UNSAFE.getLong(o-8)
    (((l >> 32) & 0xFFFFFFFFL).toInt, (l & 0xFFFFFFFFL).toInt)
  }

  @inline private[this] def packCoords(page: Int, idx: Int): Long =
    (page.toLong << 32) | idx

  private[this] def allocBlock(): Unit = {
    val b = parent.alloc(allocSize)
    UNSAFE.putLong(b, block)
    block = b
    next = b + 8
    last = b + allocSize - sliceAllocSize
    proxies += new Array[AnyRef](numBlocks)
  }

  def alloc(): Long = {
    if(freeSlice != 0L) {
      val o = freeSlice
      freeSlice = UNSAFE.getLong(o)
      o
    } else {
      if(next >= last) allocBlock()
      UNSAFE.putLong(next, packCoords(proxies.length-1, (next-block-8).toInt/sliceAllocSize))
      val o = next + 8
      next += sliceAllocSize
      o
    }
  }

  def free(o: Long): Unit = {
    val (p, i) = coordsOf(o)
    proxies(p)(i) = null
    UNSAFE.putLong(o, freeSlice)
    freeSlice = o
  }

  def getProxy(o: Long): AnyRef = {
    val (p, i) = coordsOf(o)
    proxies(p)(i)
  }

  def setProxy(o: Long, v: AnyRef): Unit = {
    val (p, i) = coordsOf(o)
    proxies(p)(i) = v
  }
}
