package de.szeiger.interact.mt

import java.util.concurrent.{BlockingQueue, CountDownLatch, LinkedBlockingQueue}
import scala.collection.mutable

class Workers[T](processors: Iterable[T => Unit]) extends mutable.Growable[T] {
  private[this] val queue: BlockingQueue[AnyRef] = new LinkedBlockingQueue[AnyRef]()
  private[this] val threads: Array[Thread] = processors.iterator.map { p =>
    val t = new Thread(new Worker(p))
    t.setDaemon(true)
    t
  }.toArray
  private[this] var active = 0
  private[this] val endMarker = new AnyRef
  private[this] val monitor = new AnyRef
  private[this] var state = 0
  @volatile private[this] var latch: CountDownLatch = _

  class Worker(p: T => Unit) extends Runnable {
    def run(): Unit = {
      var done = false
      while(!done) {
        val item = queue.take()
        if(item eq endMarker) done = true
        else {
          try p(item.asInstanceOf[T])
          finally monitor.synchronized {
            active -= 1
            if(active == 0 && latch != null) latch.countDown()
          }
        }
      }
    }
  }

  def start(): Unit = monitor.synchronized {
    assert(state == 0)
    threads.foreach(_.start)
    state = 1
  }

  def clear(): Unit = queue.clear()

  def addOne(item: T): this.type = monitor.synchronized {
    active += 1
    queue.add(item.asInstanceOf[AnyRef])
    this
  }

  def awaitEmpty(): Unit = {
    monitor.synchronized {
      assert(state == 1)
      if(active == 0) return
      latch = new CountDownLatch(1)
    }
    latch.await()
    //assert(active == 0)
    //assert(queue.isEmpty)
  }

  def shutdown(): Unit = monitor.synchronized {
    assert(state == 1)
    (0 until threads.length).foreach { _ => queue.add(endMarker) }
    state = 2
  }
}
