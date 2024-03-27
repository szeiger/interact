package de.szeiger.interact.offheap

import java.util.Arrays

object Allocator {
  val UNSAFE = {
    val f = classOf[sun.misc.Unsafe].getDeclaredField("theUnsafe")
    f.setAccessible(true)
    f.get(null).asInstanceOf[sun.misc.Unsafe]
  }

  def proxyElemOffset = -4L

  val (objArrayOffset, objArrayScale) = {
    val cl = classOf[Array[AnyRef]]
    (UNSAFE.arrayBaseOffset(cl), UNSAFE.arrayIndexScale(cl))
  }

  val (objArrayArrayOffset, objArrayArrayScale) = {
    val cl = classOf[Array[Array[AnyRef]]]
    (UNSAFE.arrayBaseOffset(cl), UNSAFE.arrayIndexScale(cl))
  }

  // used by code generator:
  def putInt(address: Long, value: Int): Unit = UNSAFE.putInt(address, value)
  def getInt(address: Long): Int = UNSAFE.getInt(address)
  def putLong(address: Long, value: Long): Unit = UNSAFE.putLong(address, value)
  def getLong(address: Long): Long = UNSAFE.getLong(address)
  def getObject(o: AnyRef, offset: Long): AnyRef = UNSAFE.getObject(o, offset)
  def putObject(o: AnyRef, offset: Long, v: AnyRef): Unit = UNSAFE.putObject(o, offset, v)
}

abstract class Allocator {
  def dispose(): Unit

  def alloc(len: Long): Long
  def alloc8(): Long = alloc(8)
  def alloc16(): Long = alloc(16)
  def alloc24(): Long = alloc(24)
  def alloc32(): Long = alloc(32)

  def free(address: Long, len: Long): Unit
  def free8(o: Long): Unit = free(o, 8)
  def free16(o: Long): Unit = free(o, 16)
  def free24(o: Long): Unit = free(o, 24)
  def free32(o: Long): Unit = free(o, 32)
}

abstract class ProxyAllocator extends Allocator {
  def getProxyPage(o: Long): AnyRef
  def getProxy(o: Long): AnyRef
  def setProxy(o: Long, v: AnyRef): Unit

  def allocProxied(len: Long): Long
  def alloc8p(): Long = allocProxied(8)
  def alloc16p(): Long = allocProxied(16)
  def alloc24p(): Long = allocProxied(24)
  def alloc32p(): Long = allocProxied(32)

  def freeProxied(o: Long, len: Long): Unit
  def free8p(o: Long): Unit = freeProxied(o, 8)
  def free16p(o: Long): Unit = freeProxied(o, 16)
  def free24p(o: Long): Unit = freeProxied(o, 24)
  def free32p(o: Long): Unit = freeProxied(o, 32)
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
  import Allocator._
  assert(blockSize % 8 == 0)
  assert(maxSliceSize % 8 == 0)
  assert(blockSize >= maxSliceSize)

  private[this] val blockAllocator = new ArenaAllocator(arenaSize)
  private[this] val slices: Array[Slice] = Array.tabulate(maxSliceSize >> 3)(i => new Slice((i+1) << 3))
  private[this] val proxySlices: Array[ProxySlice] = Array.tabulate(maxSliceSize >> 3)(i => new ProxySlice((i+1) << 3))
  private[this] var proxyPages: Array[Array[AnyRef]] = new Array[Array[AnyRef]](64)
  private[this] var proxyPagesLen: Int= 0

  private[this] val slice8: Slice = slices(8 >> 3)
  private[this] val slice16: Slice = slices(16 >> 3)
  private[this] val slice24: Slice = slices(24 >> 3)
  private[this] val slice32: Slice = slices(32 >> 3)
  private[this] val slice8p: ProxySlice = proxySlices(8 >> 3)
  private[this] val slice16p: ProxySlice = proxySlices(16 >> 3)
  private[this] val slice24p: ProxySlice = proxySlices(24 >> 3)
  private[this] val slice32p: ProxySlice = proxySlices(32 >> 3)

  override def alloc8(): Long = slice8.alloc()
  override def alloc16(): Long = slice16.alloc()
  override def alloc24(): Long = slice24.alloc()
  override def alloc32(): Long = slice32.alloc()
  override def free8(o: Long): Unit = slice8.free(o)
  override def free16(o: Long): Unit = slice16.free(o)
  override def free24(o: Long): Unit = slice24.free(o)
  override def free32(o: Long): Unit = slice32.free(o)

  override def alloc8p(): Long = slice8p.alloc()
  override def alloc16p(): Long = slice16p.alloc()
  override def alloc24p(): Long = slice24p.alloc()
  override def alloc32p(): Long = slice32p.alloc()
  override def free8p(o: Long): Unit = slice8p.free(o)
  override def free16p(o: Long): Unit = slice16p.free(o)
  override def free24p(o: Long): Unit = slice24p.free(o)
  override def free32p(o: Long): Unit = slice32p.free(o)

  def dispose(): Unit = blockAllocator.dispose()
  def alloc(len: Long): Long = slices((len >> 3).toInt).alloc()
  def free(o: Long, len: Long): Unit = slices((len >> 3).toInt).free(o)
  def allocProxied(len: Long): Long = proxySlices((len >> 3).toInt).alloc()
  def freeProxied(o: Long, len: Long): Unit = proxySlices((len >> 3).toInt).free(o)

  def getProxyPage(o: Long): AnyRef = {
    val  off = UNSAFE.getInt(o-8)
    UNSAFE.getObject(proxyPages, off)
  }

  def getProxy(o: Long): AnyRef = {
    val pp = getProxyPage(o)
    val off = UNSAFE.getInt(o-4)
    UNSAFE.getObject(pp, off)
  }

  def setProxy(o: Long, v: AnyRef): Unit = {
    val pp = getProxyPage(o)
    val off = UNSAFE.getInt(o-4)
    UNSAFE.putObject(pp, off, v)
  }

  private[this] final class Slice(sliceSize: Int) {
    private[this] val allocSize = ((blockSize / sliceSize) * sliceSize) + 8
    private[this] var block, last, next, freeSlice = 0L

    private[this] def allocBlock(): Unit = {
      val b = blockAllocator.alloc(allocSize)
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

  private[this] final class ProxySlice(_sliceSize: Int) {
    private[this] val sliceAllocSize = _sliceSize + 8
    private[this] val numBlocks = (blockSize / sliceAllocSize).toInt
    private[this] val allocSize = (numBlocks * sliceAllocSize) + 8
    private[this] var block, last, next, freeSlice = 0L

    private[this] def allocBlock(): Unit = {
      val b = blockAllocator.alloc(allocSize)
      UNSAFE.putLong(b, block)
      block = b
      next = b + 8
      last = b + allocSize - sliceAllocSize
      proxyPagesLen += 1
      if(proxyPagesLen == proxyPages.length)
        proxyPages = Arrays.copyOf(proxyPages, proxyPages.length * 2)
      proxyPages(proxyPagesLen-1) = new Array[AnyRef](numBlocks)
    }

    def alloc(): Long = {
      if(freeSlice != 0L) {
        val o = freeSlice
        freeSlice = UNSAFE.getLong(o)
        o
      } else {
        if(next >= last) allocBlock()
        val p = proxyPagesLen-1
        UNSAFE.putInt(next, objArrayArrayOffset + p*objArrayArrayScale)
        val i = (next-block-8).toInt/sliceAllocSize
        UNSAFE.putInt(next + 4, objArrayOffset + i*objArrayScale)
        val o = next + 8
        next += sliceAllocSize
        o
      }
    }

    def free(o: Long): Unit = {
      setProxy(o, null)
      UNSAFE.putLong(o, freeSlice)
      freeSlice = o
    }
  }
}
