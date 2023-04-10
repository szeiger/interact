package de.szeiger.interact.mt

import org.junit.Assert._
import org.junit.Test

import java.io.{ByteArrayOutputStream, PrintStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import java.util.concurrent.atomic.AtomicInteger
import scala.jdk.CollectionConverters._

class WorkersTest {

  @Test
  def test1(): Unit = {
    val count = new AtomicInteger(0)
    case class Task(sub: Task*)
    class Processor extends (Task => Unit) {
      def apply(t: Task): Unit = {
        count.incrementAndGet()
        t.sub.foreach { t2 =>
          Thread.sleep(50)
          ws.addOne(t2)
        }
      }
    }
    lazy val ws = new Workers[Task]((0 until 8).map(_ => new Processor))
    ws.addOne(Task())
    ws.start()
    ws.addOne(Task(Task(Task(), Task(Task(), Task())), Task(Task(), Task(), Task())))
    ws.awaitEmpty()
    assertEquals(11, count.get())
    ws.addOne(Task(Task(Task(), Task(Task(), Task())), Task(Task(), Task(), Task())))
    ws.awaitEmpty()
    assertEquals(21, count.get())
    ws.shutdown()
  }
}
