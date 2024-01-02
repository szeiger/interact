package de.szeiger.interact

import scala.collection.mutable

class ExecutionMetrics {
  private[this] final class MutInt(var i: Int)
  private[this] var steps, cellAlloc, cellReuse, singletonUse, loopSave = 0
  private[this] var metrics = mutable.Map.empty[String, MutInt]

  def getSteps: Int = steps

  @inline def recordStats(cellAllocations: Int, cachedCellReuse: Int, singletonUse: Int, loopSave: Int): Unit = {
    this.steps += 1
    this.cellAlloc += cellAllocations
    this.cellReuse += cachedCellReuse
    this.singletonUse += singletonUse
    this.loopSave += loopSave
  }

  @inline def recordStats(cellAllocations: Int): Unit = steps += 1

  def recordMetric(metric: String, inc: Int = 1): Unit = {
    val m = metrics.getOrElseUpdate(metric, new MutInt(0))
    m.i += inc
  }

  def log(): Unit = {
    logStats()
    logMetrics()
  }
  def logStats(): Unit = {
    println(s"Steps: ${steps} (${steps-loopSave} non-looping), cells created: ${cellAlloc} new, ${cellReuse} cached, ${singletonUse} singleton")
  }
  def logMetrics(): Unit = {
    val data = metrics.toVector.sortBy(_._1).map { case (k, v) => (k, v.i.toString) }
    val maxLen = data.iterator.map { case (k, v) => k.length + v.length }.max
    data.foreach { case (k, v) =>
      val pad = " " * (maxLen-k.length-v.length)
      println(s"  $k   $pad$v")
    }
  }
}
