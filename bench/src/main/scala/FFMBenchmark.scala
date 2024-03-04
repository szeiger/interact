package de.szeiger.interact

import de.szeiger.interact.stc2.Allocator
import org.openjdk.jmh.annotations._
import org.openjdk.jmh.infra._

//import java.lang.foreign.MemoryLayout.PathElement
import java.util.concurrent.TimeUnit
//import java.lang.foreign._
import java.nio.ByteBuffer

@BenchmarkMode(Array(Mode.AverageTime))
@Fork(value = 1, jvmArgsAppend = Array("-Xmx12g", "-Xss32M", "-XX:+UnlockExperimentalVMOptions", "-XX:+UseZGC", "--enable-native-access=ALL-UNNAMED"))
@Threads(1)
@Warmup(iterations = 10, time = 1)
@Measurement(iterations = 10, time = 1)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
class FFMBenchmark {
  val u = {
    val f = classOf[sun.misc.Unsafe].getDeclaredField("theUnsafe")
    f.setAccessible(true)
    f.get(null).asInstanceOf[sun.misc.Unsafe]
  }

  println()
  println("heap: " + heap0())
//  println("heapByteByffer: " + heapByteBuffer0())
  //println("autoArena: " + autoArena0())
//  println("customAllocator: " + customAllocator0())
//  println("customAllocatorDirect: " + customAllocatorDirect0())
  //println("ffmByteBuffer: " + ffmByteBuffer0())
  //println("unsafe: " + unsafe0())
  println("unsafeCustom: " + unsafeCustom0())
  println("unsafeAllocator: " + unsafeAllocator0())

  @Benchmark
  def heap(bh: Blackhole): Unit = bh.consume(heap0())

//  @Benchmark
//  def heapByteBuffer(bh: Blackhole): Unit = bh.consume(heapByteBuffer0())

  //@Benchmark
  //def autoArena(bh: Blackhole): Unit = bh.consume(autoArena0())

//  @Benchmark
//  def customAllocator(bh: Blackhole): Unit = bh.consume(customAllocator0())
//
//  @Benchmark
//  def customAllocatorDirect(bh: Blackhole): Unit = bh.consume(customAllocatorDirect0())

  //@Benchmark
  //def ffmByteBuffer(bh: Blackhole): Unit = bh.consume(ffmByteBuffer0())

  //@Benchmark
  //def unsafe(bh: Blackhole): Unit = bh.consume(unsafe0())

  @Benchmark
  def unsafeCustom(bh: Blackhole): Unit = bh.consume(unsafeCustom0())

  @Benchmark
  def unsafeAllocator(bh: Blackhole): Unit = bh.consume(unsafeAllocator0())

  def heap0(): Long = {
    final class C(var c0: C, var p0: Int, var c1: C, var p1: Int)
    val buf = new Array[C](10000000)
    for(i <- buf.indices) buf(i) = new C(null, 0, null, 0)
    for(i <- 1 until buf.length-1) {
      buf(i).c0 = buf(i - 1)
      buf(i).p0 = -1
      buf(i).c1 = buf(i + 1)
      buf(i).p1 = i
    }
    var sum = 0L
    for(i <- 1 until buf.length-1) {
      sum += buf(i).p1
      sum -= buf(i).c0.p1
    }
    sum
  }

  def heapByteBuffer0(): Long = {
    val buf = new Array[Int](10000000)
    val bb = ByteBuffer.allocateDirect(buf.length * 24)
    var next = 0
    def alloc(len: Int): Int = {
      val a = next
      next += len
      a
    }
    for(i <- buf.indices) buf(i) = alloc(24)
    for(i <- 1 until buf.length-1) {
      bb.putLong(buf(i), buf(i-1))
      bb.putLong(buf(i)+8, buf(i+1))
      bb.putInt(buf(i)+16, -1)
      bb.putInt(buf(i)+20, i)
    }
    var sum = 0L
    for(i <- 1 until buf.length-1) {
      sum += bb.getInt(buf(i)+20)
      sum -= bb.getInt(bb.getLong(buf(i)).toInt+20)
    }
    sum
  }

//  def autoArena0(): Long = {
//    import LayoutGlobals._
//    val arena = Arena.ofAuto()
//    val buf = new Array[MemorySegment](10000000)
//    for(i <- buf.indices) buf(i) = arena.allocate(layout)
//    for(i <- 1 until buf.length-1) {
//      c0vh.set(buf(i), 0, buf(i-1))
//      c1vh.set(buf(i), 0, buf(i+1))
//      p0vh.set(buf(i), 0, -1)
//      p1vh.set(buf(i), 0, i)
//    }
//    var sum = 0L
//    for(i <- 1 until buf.length-1) {
//      sum += p1vh.get(buf(i), 0).asInstanceOf[Int]
//      sum -= p1vh.get(c0vh.get(buf(i), 0).asInstanceOf[MemorySegment].reinterpret(layout.byteSize()), 0).asInstanceOf[Int]
//    }
//    sum
//  }
//
//  def customAllocator0(): Long = {
//    import LayoutGlobals2S._
//    val arena = Arena.ofAuto()
//    val buf = new Array[Long](10000000)
//    val _block = arena.allocate(buf.length * 24)
//    val root = MemorySegment.NULL.reinterpret(Long.MaxValue)
//    var next = _block.address()
//    def alloc(len: Int): Long = {
//      val a = next
//      next += len
//      a
//    }
//    for(i <- buf.indices) buf(i) = alloc(24)
//    for(i <- 1 until buf.length-1) {
//      c0vh.set(root, buf(i), buf(i-1))
//      c1vh.set(root, buf(i), buf(i+1))
//      p0vh.set(root, buf(i), -1)
//      p1vh.set(root, buf(i), i)
//    }
//    var sum = 0L
//    for(i <- 1 until buf.length-1) {
//      sum += p1vh.get(root, buf(i)).asInstanceOf[Int]
//      sum -= p1vh.get(root, c0vh.get(root, buf(i)).asInstanceOf[Long]).asInstanceOf[Int]
//    }
//    sum
//  }
//
//  def customAllocatorDirect0(): Long = {
//    val arena = Arena.ofAuto()
//    val buf = new Array[Long](10000000)
//    val _block = arena.allocate(buf.length * 24)
//    val off = _block.address()
//    val root = MemorySegment.NULL.reinterpret(Long.MaxValue)
//    var next = off
//    def alloc(len: Int): Long = {
//      val a = next
//      next += len
//      a
//    }
//    for(i <- buf.indices) buf(i) = alloc(24)
//    for(i <- 1 until buf.length-1) {
//      root.set(ValueLayout.JAVA_LONG, buf(i), buf(i-1))
//      root.set(ValueLayout.JAVA_LONG, buf(i)+8, buf(i+1))
//      root.set(ValueLayout.JAVA_INT, buf(i)+16, -1)
//      root.set(ValueLayout.JAVA_INT, buf(i)+20, i)
//    }
//    var sum = 0L
//    for(i <- 1 until buf.length-1) {
//      sum += root.get(ValueLayout.JAVA_INT, buf(i)+20)
//      sum -= root.get(ValueLayout.JAVA_INT, root.get(ValueLayout.JAVA_LONG, buf(i))+20)
//    }
//    sum
//  }
//
//  def ffmByteBuffer0(): Long = {
//    val arena = Arena.ofAuto()
//    val buf = new Array[Int](10000000)
//    val bb = arena.allocate(buf.length * 24).asByteBuffer()
//    var next = 0
//    def alloc(len: Int): Int = {
//      val a = next
//      next += len
//      a
//    }
//    for(i <- buf.indices) buf(i) = alloc(24)
//    for(i <- 1 until buf.length-1) {
//      bb.putLong(buf(i), buf(i-1))
//      bb.putLong(buf(i)+8, buf(i+1))
//      bb.putInt(buf(i)+16, -1)
//      bb.putInt(buf(i)+20, i)
//    }
//    var sum = 0L
//    for(i <- 1 until buf.length-1) {
//      sum += bb.getInt(buf(i)+20)
//      sum -= bb.getInt(bb.getLong(buf(i)).toInt+20)
//    }
//    sum
//  }

  def unsafe0(): Long = {
    val buf = new Array[Long](10000000)
    for(i <- buf.indices) buf(i) = u.allocateMemory(24)
    for(i <- 1 until buf.length-1) {
      u.putLong(buf(i), buf(i-1))
      u.putLong(buf(i)+8, buf(i+1))
      u.putInt(buf(i)+16, -1)
      u.putInt(buf(i)+20, i)
    }
    var sum = 0L
    for(i <- 1 until buf.length-1) {
      sum += u.getInt(buf(i)+20)
      sum -= u.getInt(u.getAddress(buf(i))+20)
    }
    for(i <- buf.indices) u.freeMemory(buf(i))
    sum
  }

  def unsafeCustom0(): Long = {
    val buf = new Array[Long](10000000)
    val block = u.allocateMemory(buf.length * 24)
    var next = block
    def alloc(len: Int): Long = {
      val a = next
      next += len
      a
    }
    for(i <- buf.indices) buf(i) = alloc(24)
    for(i <- 1 until buf.length-1) {
      u.putLong(buf(i), buf(i-1))
      u.putLong(buf(i)+8, buf(i+1))
      u.putInt(buf(i)+16, -1)
      u.putInt(buf(i)+20, i)
    }
    var sum = 0L
    for(i <- 1 until buf.length-1) {
      sum += u.getInt(buf(i)+20)
      sum -= u.getInt(u.getAddress(buf(i))+20)
    }
    u.freeMemory(block)
    sum
  }

  def unsafeAllocator0(): Long = {
    val buf = new Array[Long](10000000)
    val a = new Allocator
    for(i <- buf.indices) buf(i) = a.alloc(24)
    for(i <- 1 until buf.length-1) {
      Allocator.setLong(buf(i), buf(i-1))
      Allocator.setLong(buf(i)+8, buf(i+1))
      Allocator.setInt(buf(i)+16, -1)
      Allocator.setInt(buf(i)+20, i)
    }
    var sum = 0L
    for(i <- 1 until buf.length-1) {
      sum += Allocator.getInt(buf(i)+20)
      sum -= Allocator.getInt(Allocator.getLong(buf(i))+20)
    }
    a.dispose()
    sum
  }
}

//object LayoutGlobals {
//  val layout = MemoryLayout.structLayout(
//    ValueLayout.ADDRESS.withName("c0"),
//    ValueLayout.ADDRESS.withName("c1"),
//    ValueLayout.JAVA_INT.withName("p0"),
//    ValueLayout.JAVA_INT.withName("p1"),
//  )
//  val c0vh = layout.varHandle(PathElement.groupElement("c0"))
//  val p0vh = layout.varHandle(PathElement.groupElement("p0"))
//  val c1vh = layout.varHandle(PathElement.groupElement("c1"))
//  val p1vh = layout.varHandle(PathElement.groupElement("p1"))
//}
//
//object LayoutGlobals2S {
//  val layout = MemoryLayout.structLayout(
//    ValueLayout.JAVA_LONG.withName("c0"),
//    ValueLayout.JAVA_LONG.withName("c1"),
//    ValueLayout.JAVA_INT.withName("p0"),
//    ValueLayout.JAVA_INT.withName("p1"),
//  )
//  val c0vh = layout.varHandle(PathElement.groupElement("c0"))
//  val p0vh = layout.varHandle(PathElement.groupElement("p0"))
//  val c1vh = layout.varHandle(PathElement.groupElement("c1"))
//  val p1vh = layout.varHandle(PathElement.groupElement("p1"))
//}
