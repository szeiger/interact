package de.szeiger.interact

import de.szeiger.interact.ast.Symbol

import scala.collection.mutable

final class SymCounts(private val m: mutable.Map[Symbol, Int]) extends AnyVal {
  override def toString: String = {
    m.iterator.filter(_._2 > 0).toVector.sortBy(_._1.id).map {
      case (s, 1) => s.id
      case (s, i) => s"$i ${s.id}"
    }.mkString("[", ", ", "]")
  }

  def size = m.size

  def + (s: Symbol): SymCounts = {
    val n = mutable.Map.from(m)
    SymCounts.add(n, s, 1)
    new SymCounts(n)
  }

  def - (s: Symbol): SymCounts = {
    val n = mutable.Map.from(m)
    SymCounts.add(n, s, -1)
    new SymCounts(n)
  }

  def ++ (o: SymCounts): SymCounts = {
    val n = mutable.Map.from(m)
    o.m.foreach { case (k, v) => SymCounts.add(n, k, v) }
    new SymCounts(n)
  }

  def ++ (it: IterableOnce[Symbol]): SymCounts = {
    val n = mutable.Map.from(m)
    it.iterator.foreach(SymCounts.add(n, _, 1))
    new SymCounts(n)
  }

  def -- (o: SymCounts): SymCounts = {
    val n = mutable.Map.from(m)
    o.m.foreach { case (k, v) => SymCounts.add(n, k, -v) }
    new SymCounts(n)
  }

  def count(s: Symbol): Int = m.getOrElse(s, 0)

  def contains(s: Symbol): Boolean = count(s) > 0
}

object SymCounts {
  private def add(m: mutable.Map[Symbol, Int], s: Symbol, count: Int): Unit =
    m.updateWith(s) {
      case Some(i) =>
        val j = i+count
        if(j > 0) Some(j) else None
      case None if count > 0 => Some(count)
      case None => None
    }

  private def add(m: mutable.Map[Symbol, Int], it: IterableOnce[Symbol]): Unit = it.iterator.foreach(add(m, _, 1))

  def apply(ss: Symbol*): SymCounts = {
    val m = mutable.Map.empty[Symbol, Int]
    add(m, ss)
    new SymCounts(m)
  }

  def from(syms: IterableOnce[Symbol]): SymCounts = {
    val m = mutable.Map.empty[Symbol, Int]
    add(m, syms)
    new SymCounts(m)
  }

  val empty = from(Nil)
}
