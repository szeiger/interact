package de.szeiger.interact.codegen

import java.lang.invoke.VarHandle
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.{CountedCompleter, ForkJoinPool}
import scala.annotation.tailrec

object ParSupport {
  val parallelism: Int = {
    val s = System.getProperty("interact.compilerParallelism", "")
    if(s.nonEmpty) s.toInt
    else math.min(ForkJoinPool.commonPool().getParallelism, 8)
  }

  final class AtomicCounter {
    private[this] val ai = new AtomicInteger(0)

    @tailrec def max(i: Int): Unit = {
      val v = ai.get()
      if(i > v && !ai.compareAndSet(v, i)) max(i)
    }

    def get: Int = ai.get()
  }

  def foreach[T >: Null <: AnyRef](a: Iterable[T])(f: T => Unit): Unit = {
    if(parallelism <= 1) a.foreach(f)
    else {
      val it = a.iterator
      def getNext: T = it.synchronized { if(it.hasNext) it.next() else null }
      final class Task(parent: CountedCompleter[_]) extends CountedCompleter[Null](parent) {
        @tailrec def compute: Unit = getNext match {
          case null =>
            VarHandle.releaseFence()
            propagateCompletion()
          case v =>
            f(v)
            compute
        }
      }
      (new CountedCompleter[Null](null, parallelism) {
        override def compute(): Unit = {
          for(i <- 1 to parallelism) new Task(this).fork()
          propagateCompletion()
        }
      }).invoke()
    }
  }
}
