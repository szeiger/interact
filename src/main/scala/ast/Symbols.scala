package de.szeiger.interact.ast

import scala.collection.mutable

final class Symbol private[ast] (val id: String, val arity: Int = 0, val returnArity: Int = 1,
    val isCons: Boolean = false, val isDef: Boolean = false,
    val payloadType: PayloadType = PayloadType.VOID, val matchContinuationPort: Int = -2,
    val isEmbedded: Boolean = false) {
  def callArity: Int = arity + 1 - returnArity
  def hasPayload: Boolean = payloadType != PayloadType.VOID
  override def toString: String = id
  def isDefined: Boolean = this != Symbol.NoSymbol
  def isEmpty: Boolean = !isDefined
}

object Symbol {
  val NoSymbol = new Symbol("<NoSymbol>")
}

class Symbols(parent: Option[Symbols] = None) {
  private val syms = mutable.HashMap.empty[String, Symbol]
  def define(id: String, isCons: Boolean = false, isDef: Boolean = false, arity: Int = 0, returnArity: Int = 1,
      payloadType: PayloadType = PayloadType.VOID, matchContinuationPort: Int = -2,
      isEmbedded: Boolean = false): Symbol = {
    assert(get(id).isEmpty)
    val sym = new Symbol(id, arity, returnArity, isCons, isDef, payloadType, matchContinuationPort, isEmbedded)
    syms.put(id, sym)
    sym
  }
  def getOrAdd(id: String): Symbol = get(id).getOrElse(define(id))
  def get(id: String): Option[Symbol] =
    (parent match {
      case Some(p) => p.syms.get(id)
      case None => None
    }).orElse(syms.get(id))
  def apply(id: String): Symbol =
    get(id).getOrElse(sys.error(s"No symbol found for $id"))
  def symbols: Iterator[Symbol] = syms.valuesIterator ++ parent.map(_.symbols).getOrElse(Iterator.empty)
  override def toString: String = s"Symbols(${syms.map { case (_, v) => s"$v"}.mkString(", ")})"
  def sub(): Symbols = new Symbols(Some(this))
}

class RefsMap {
  private[this] val data = mutable.Map.empty[Symbol, Int]
  def inc(s: Symbol): Unit = data.update(s, apply(s) + 1)
  def apply(s: Symbol): Int = data.getOrElse(s, 0)
  def free: Iterator[Symbol] = data.iterator.filter(_._2 == 1).map(_._1)
  def linear: Iterator[Symbol] = data.iterator.filter(_._2 == 2).map(_._1)
  def err: Iterator[Symbol] = data.iterator.filter(_._2 > 2).map(_._1)
}
