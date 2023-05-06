package de.szeiger.interact.mt.workers

import java.lang.invoke.MethodHandles
import scala.annotation.tailrec

object Workers {
  private[workers] final val endMarker = new AnyRef
}

abstract class Worker[T >: Null] extends Thread {
  import Worker._

  private[workers] final var _workers: Workers[T] = _
  private[workers] final var _idx: Int = _
  private[workers] final var page: Page = _

  @inline final def workers = _workers
  @inline final def idx = _idx

  @volatile private[this] var _state: Int = 0

  def apply(v: T): Unit

  final override def run(): Unit = {
    while(true) {
      var item = tryTake()
      if(item == null) {
        maybeEmpty()
        item = take()
      }
      if(item.asInstanceOf[AnyRef] eq Workers.endMarker) return
      apply(item)
    }
  }

  def maybeEmpty(): Unit = ()

  @inline private def tryLock(): Boolean = STATE.weakCompareAndSetAcquire(this, 0, 1)

  @tailrec @inline private final def lock(): Boolean = {
    if(tryLock()) true
    else {
      Thread.onSpinWait()
      lock()
    }
  }

  @inline private final def unlock(): Unit = STATE.setRelease(this, 0)

  final def add(v: T): Unit = {
    //println(s"add($v)")
    lock()
    val p = page
    if(p.size < p.data.length) {
      p.data(p.size) = v.asInstanceOf[AnyRef]
      p.size += 1
    } else {
      val p2 = new Page(workers.pageSize)
      p2.next = p
      p2.data(0) = v.asInstanceOf[AnyRef]
      p2.size = 1
      page = p2
    }
    unlock()
    //println(s"add($v) - done")
  }

  private final def tryTake(): T = {
    if(tryLock()) {
      val v = page.takeOrNull()
      val ret = if(v != null) {
        v
      } else if(page.next != null) {
        page = page.next
        page.takeOrNull()
      } else {
        val p = tryStealFromOther(page, (idx+1) % workers.numThreads, workers.numThreads-1)
        if(p != null) {
          page = p
          p.takeOrNull()
        } else null
      }
      unlock()
      ret.asInstanceOf[T]
    } else null
  }

  @tailrec private final def take(): T = {
    val ret = tryTake()
    if(ret != null) ret
    else {
      Thread.onSpinWait()
      take()
    }
  }

  private final def trySteal(into: Page): Page = {
    if(!tryLock()) null
    else {
      val ret = if(page.next != null) {
        val p = page.next
        page.next = null
        p
      } else if(page.size == 0) null
      else if(page.size == 1) {
        val p = page
        page = into
        p
      } else {
        val stealCount = page.size/2
        page.size -= stealCount
        into.size = stealCount
        System.arraycopy(page.data, page.size, into.data, 0, stealCount)
        into
      }
      unlock()
      ret
    }
  }

  @tailrec private final def tryStealFromOther(into: Page, cur: Int, left: Int): Page = {
    val p = workers.workers(cur).trySteal(into)
    if(p != null) p
    else if(left > 0) tryStealFromOther(into, (cur+1) % workers.numThreads, left-1)
    else null
  }
}

object Worker {
  final val STATE =
    MethodHandles.privateLookupIn(classOf[Worker[_]], MethodHandles.lookup).findVarHandle(classOf[Worker[_]], "_state", classOf[Int])
}

class Workers[T >: Null](val numThreads: Int, val pageSize: Int, createWorker: Int => Worker[T]) {
  val workers = (0 until numThreads).iterator.map { i =>
    val w = createWorker(i)
    w.setDaemon(true)
    w.page = new Page(pageSize)
    w._workers = this
    w._idx = i
    w
  }.toArray
  private[this] var started = false
  private[this] var addIdx = 0

  def add(item: T): Unit = {
    workers(addIdx).add(item)
    addIdx = (addIdx+1) % numThreads
  }

  def start(): Unit = {
    if(!started) {
      workers.foreach(_.start)
      started = true
    }
  }

  def shutdown(): Unit = {
    (1 to workers.length).foreach { _ => add(Workers.endMarker.asInstanceOf[T]) }
    workers.foreach(_.join())
  }
}

final class Page(_pageSize: Int) {
  val data = new Array[AnyRef](_pageSize)
  var size: Int = 0
  var next: Page = _

  def takeOrNull(): AnyRef =
    if(size > 0) { size -= 1; data(size) } else null
}
