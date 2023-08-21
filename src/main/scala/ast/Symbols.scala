package de.szeiger.interact.ast

import de.szeiger.interact.CompilerResult

import scala.collection.mutable

final class Symbol(val id: String, val arity: Int = 0, val returnArity: Int = 1,
    val isCons: Boolean = false, val isDef: Boolean = false,
    var payloadType: PayloadType = PayloadType.VOID, val matchContinuationPort: Int = -2,
    val isEmbedded: Boolean = false) {
  def callArity: Int = arity + 1 - returnArity
  def hasPayload: Boolean = payloadType != PayloadType.VOID
  override def toString: String = id
  def isDefined: Boolean = this != Symbol.NoSymbol
  def isEmpty: Boolean = !isDefined
  def uniqueStr: String = if(isDefined) s"$id @ ${System.identityHashCode(this)}" else "<NoSymbol>"
}

object Symbol {
  val NoSymbol = new Symbol("<NoSymbol>")
}

class Symbols(parent: Option[Symbols] = None) {
  private[this] val syms = mutable.HashMap.empty[String, Symbol]
  def define(id: String, isCons: Boolean = false, isDef: Boolean = false, arity: Int = 0, returnArity: Int = 1,
      payloadType: PayloadType = PayloadType.VOID, matchContinuationPort: Int = -2,
      isEmbedded: Boolean = false): Symbol = {
    assert(get(id).isEmpty)
    val sym = new Symbol(id, arity, returnArity, isCons, isDef, payloadType, matchContinuationPort, isEmbedded)
    syms.put(id, sym)
    sym
  }
  def defineCons(id: String, arity: Int, payloadType: PayloadType): Symbol =
    define(id, isCons = true, arity = arity, payloadType = payloadType)
  def defineDef(id: String, argLen: Int, retLen: Int, payloadType: PayloadType): Symbol =
    define(id, isCons = true, isDef = true, arity = argLen + retLen - 1, returnArity = retLen, payloadType = payloadType)
  def getOrAdd(id: Ident): Symbol = get(id).getOrElse(define(id.s))
  def contains(id: Ident): Boolean = get(id).isDefined
  def containsLocal(id: Ident): Boolean = syms.contains(id.s)
  def get(id: Ident): Option[Symbol] = get(id.s)
  def get(id: String): Option[Symbol] = syms.get(id).orElse(parent.flatMap(_.get(id)))
  def apply(id: Ident): Symbol = apply(id.s)
  def apply(id: String): Symbol =
    get(id).getOrElse(sys.error(s"No symbol found for $id"))
  def symbols: Iterator[Symbol] = syms.valuesIterator ++ parent.map(_.symbols).getOrElse(Iterator.empty)
  def sub(): Symbols = new Symbols(Some(this))
  override def toString: String = s"Symbols(${syms.map { case (_, v) => s"$v"}.mkString(", ")})"
}

class RefsMap(parent: Option[RefsMap] = None) {
  private[this] val data = mutable.Map.empty[Symbol, Int]
  private[this] val hasErr = mutable.Set.empty[Symbol]
  def inc(s: Symbol): Unit = data.update(s, {
    val c = apply(s) + 1
    if(c == 3) {
      if(!s.isEmbedded || !s.payloadType.canCopy) hasErr += s
    }
    c
  })
  def local: Iterator[(Symbol, Int)] = data.iterator.map {case (s, c) =>
    (s, c - parent.map(_(s)).getOrElse(0))
  }.filter(_._2 > 0)
  def iterator: Iterator[(Symbol, Int)] = parent match {
    case Some(r) => r.iterator.filter(t => !data.contains(t._1)) ++ data.iterator
    case None => data.iterator
  }
  def apply(s: Symbol): Int = data.getOrElse(s, parent match {
    case Some(r) => r(s)
    case None => 0
  })
  def free: Iterator[Symbol] = iterator.filter(_._2 == 1).map(_._1)
  def linear: Iterator[Symbol] = iterator.filter(_._2 == 2).map(_._1)
  def err: Iterator[Symbol] = parent match {
    case Some(r) => r.err ++ hasErr.iterator
    case None => hasErr.iterator
  }
  def nonFree: Iterator[Symbol] = iterator.filter(_._2 > 1).map(_._1)
  def hasNonFree: Boolean = hasErr.nonEmpty || linear.hasNext || parent.exists(_.hasNonFree)
  def hasError: Boolean = hasErr.nonEmpty || parent.exists(_.hasError)
  def collect(n: Node): Unit = n match {
    case n: Ident => if(!n.sym.isEmpty && !n.sym.isCons) inc(n.sym)
    case n => n.nodeChildren.foreach(collect)
  }
  def sub(): RefsMap = parent match {
    case Some(r) if data.isEmpty => r.sub()
    case _ => new RefsMap(Some(this))
  }
  def allSymbols: Iterator[Symbol] = iterator.map(_._1).filter(_.isDefined)
}
