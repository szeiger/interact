package de.szeiger.interact.mt

import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.{BlockingQueue, CountDownLatch, LinkedBlockingQueue}
import scala.collection.mutable

class Workers[T](numThreads: Int, createProcessor: Workers[T] => T => Unit) extends mutable.Growable[T] {
  private[this] val queue: BlockingQueue[AnyRef] = new LinkedBlockingQueue[AnyRef]()
  private[this] val threads: Array[Thread] = (1 to numThreads).iterator.map { _ =>
    val t = new Thread(new Worker(createProcessor(this)))
    t.setDaemon(true)
    t
  }.toArray
  private[this] val active = new AtomicInteger()
  private[this] var started = false
  private[this] val endMarker = new AnyRef
  @volatile private[this] var latch: CountDownLatch = _

  class Worker(p: T => Unit) extends Runnable {
    def run(): Unit = {
      var done = false
      while(!done) {
        val item = queue.take()
        if(item eq endMarker) done = true
        else {
          try p(item.asInstanceOf[T])
          if(active.addAndGet(-1) == 0) latch.countDown()
        }
      }
    }
  }

  def start(): Unit = {
    active.incrementAndGet()
    latch = new CountDownLatch(1)
    if(!started) {
      threads.foreach(_.start)
      started = true
    }
  }

  def clear(): Unit = queue.clear()

  def addOne(item: T): this.type = {
    active.incrementAndGet()
    queue.add(item.asInstanceOf[AnyRef])
    this
  }

  def awaitEmpty(): Unit = {
    if(active.addAndGet(-1) != 0)
      latch.await()
  }

  def shutdown(): Unit =
    (0 until threads.length).foreach { _ => queue.add(endMarker) }
}
