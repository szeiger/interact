package de.szeiger.interact.mt

import de.szeiger.interact.mt.workers.{Worker, Workers}
import org.junit.Assert._
import org.junit.Test

import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicInteger

class WorkersTest {

  @Test
  def test1(): Unit = {
    val unfinished = new AtomicInteger(0)
    var latch: CountDownLatch = new CountDownLatch(1)
    val count = new AtomicInteger(0)
    case class Task(sub: Task*)
    def add(t: Task): Unit = {
      unfinished.incrementAndGet()
      ws.add(t)
    }
    class Processor extends Worker[Task] {
      def apply(t: Task): Unit = {
        count.incrementAndGet()
        t.sub.foreach { t2 =>
          Thread.sleep(50)
          unfinished.incrementAndGet()
          this.add(t2)
        }
        if(unfinished.decrementAndGet() == 0) latch.countDown()
      }
    }
    lazy val ws = new Workers[Task](8, 1024, _ => new Processor)
    add(Task())
    ws.start()
    add(Task(Task(Task(), Task(Task(), Task())), Task(Task(), Task(), Task())))
    while(unfinished.get() != 0) latch.await()
    assertEquals(11, count.get())
    latch = new CountDownLatch(1)
    add(Task(Task(Task(), Task(Task(), Task())), Task(Task(), Task(), Task())))
    while(unfinished.get() != 0) latch.await()
    assertEquals(21, count.get())
    ws.shutdown()
  }
}
