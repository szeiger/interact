package de.szeiger.interact.ast

import scala.collection.mutable

final class Symbol(val id: String, val arity: Int = 0, val returnArity: Int = 1, var payloadType: PayloadType = PayloadType.VOID,
  val matchContinuationPort: Int = -2, private[this] var _flags: Int = 0) {
  import Symbol._

  def flags: Int = _flags
  def isCons: Boolean = (_flags & FLAG_CONS) != 0
  def isDef: Boolean = (_flags & FLAG_DEF) != 0
  def isEmbedded: Boolean = (_flags & FLAG_EMBEDDED) != 0
  def isPattern: Boolean = (_flags & FLAG_PATTERN) != 0

  def setPattern(): Unit = _flags = (_flags | FLAG_PATTERN)

  def isContinuation: Boolean = matchContinuationPort != -2
  def callArity: Int = arity + 1 - returnArity
  def hasPayload: Boolean = payloadType != PayloadType.VOID
  override def toString: String = id
  def isDefined: Boolean = this != Symbol.NoSymbol
  def isEmpty: Boolean = !isDefined
  def uniqueStr: String = if(isDefined) s"$id:${System.identityHashCode(this)}" else "<NoSymbol>"
  def show: String = s"$uniqueStr<$payloadType>"
}

object Symbol {
  def apply(id: String, arity: Int = 0, returnArity: Int = 1,
      isCons: Boolean = false, isDef: Boolean = false,
      payloadType: PayloadType = PayloadType.VOID, matchContinuationPort: Int = -2,
      isEmbedded: Boolean = false, isPattern: Boolean = false): Symbol =
    new Symbol(id, arity, returnArity, payloadType, matchContinuationPort,
      (if(isCons) FLAG_CONS else 0) | (if(isDef) FLAG_DEF else 0) | (if(isEmbedded) FLAG_EMBEDDED else 0) | (if(isPattern) FLAG_PATTERN else 0)
    )

  val FLAG_CONS         = 1 << 0
  val FLAG_DEF          = 1 << 1
  val FLAG_EMBEDDED     = 1 << 2
  val FLAG_PATTERN      = 1 << 3

  val NoSymbol = new Symbol("<NoSymbol>")
}

class SymbolGen(prefix2: String, isEmbedded: Boolean = false, payloadType: PayloadType = PayloadType.VOID) {
  private[this] var last = 0
  def apply(isEmbedded: Boolean = isEmbedded, payloadType: PayloadType = payloadType, prefix: String = ""): Symbol = {
    last += 1
    Symbol(prefix+prefix2+last, isEmbedded = isEmbedded, payloadType = payloadType)
  }
  def id(isEmbedded: Boolean = isEmbedded, payloadType: PayloadType = payloadType, prefix: String = ""): Ident = {
    val s = apply(isEmbedded, payloadType, prefix)
    val i = Ident(s.id)
    i.sym = s
    i
  }
}

class Symbols(parent: Option[Symbols] = None) {
  private[this] val syms = mutable.HashMap.empty[String, Symbol]
  def define(id: String, isCons: Boolean = false, isDef: Boolean = false, arity: Int = 0, returnArity: Int = 1,
      payloadType: PayloadType = PayloadType.VOID, matchContinuationPort: Int = -2,
      isEmbedded: Boolean = false): Symbol = {
    assert(get(id).isEmpty)
    val sym = Symbol(id, arity, returnArity, isCons, isDef, payloadType, matchContinuationPort, isEmbedded)
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
  private[this] def collect0(n: Node, embedded: Boolean, regular: Boolean): Unit = n match {
    case n: Ident =>
      val use = (n.sym.isEmbedded && embedded) || (!n.sym.isEmbedded && regular)
      if(use && !n.sym.isEmpty && !n.sym.isCons) inc(n.sym)
    case n => n.nodeChildren.foreach(collect0(_, embedded, regular))
  }
  def collectRegular(n: Node): Unit = collect0(n, false, true)
  def collectEmbedded(n: Node): Unit = collect0(n, true, false)
  def collectAll(n: Node): Unit = collect0(n, true, true)
  def sub(): RefsMap = parent match {
    case Some(r) if data.isEmpty => r.sub()
    case _ => new RefsMap(Some(this))
  }
  def allSymbols: Iterator[Symbol] = iterator.map(_._1).filter(_.isDefined)
}
