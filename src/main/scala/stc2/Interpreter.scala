package de.szeiger.interact.stc2

import de.szeiger.interact.codegen.{ClassWriter, LocalClassLoader}
import de.szeiger.interact._
import de.szeiger.interact.ast.{CompilationUnit, PayloadType, Symbol, Symbols}
import de.szeiger.interact.offheap.{Allocator, MemoryDebugger, ProxyAllocator}

import java.util.Arrays
import scala.collection.mutable

object Defs {
  type Cell = Long
}
import Defs._

abstract class InitialRuleImpl {
  def reduce(a0: Cell, a1: Cell, ptw: Interpreter): Unit
  def freeWires: Array[Symbol]
}

abstract class Dispatch {
  def reduce(c1: Cell, c2: Cell, level: Int, ptw: Interpreter): Unit
}

final class Interpreter(globals: Symbols, compilationUnit: CompilationUnit, config: Config) extends BaseInterpreter { self =>
  import Interpreter._

  private[this] val symIds = globals.symbols.filter(_.isCons).toVector.sortBy(_.id).iterator.zipWithIndex.toMap
  private[this] val reverseSymIds = symIds.map { case (sym, idx) => (idx, sym) }
  private[this] val (initialRuleImpls: Vector[InitialRuleImpl], dispatch: Dispatch) = {
    val lcl = new LocalClassLoader
    val cw = ClassWriter(config, lcl)
    val (initial, dispN) = new CodeGen("generated", cw, compilationUnit, globals, symIds, config).compile()
    cw.close()
    val irs = initial.map { cln => lcl.loadClass(cln).getDeclaredConstructor().newInstance().asInstanceOf[InitialRuleImpl] }
    val disp = lcl.loadClass(dispN).getDeclaredConstructor().newInstance().asInstanceOf[Dispatch]
    (irs, disp)
  }
  private[this] val cutBuffer, irreducible = new CutBuffer(16)
  private[this] val freeWires = mutable.HashSet.empty[Cell]
  private[this] val freeWireLookup = mutable.HashMap.empty[Int, Symbol]
  private[this] var metrics: ExecutionMetrics = _
  private[this] var allocator: ProxyAllocator = _
  private[this] val singletons: Array[Cell] = new Array(symIds.size)
  private[this] var nextLabel = Long.MinValue
  private[this] val tailCallDepth = config.tailCallDepth

  def getMetrics: ExecutionMetrics = metrics

  def getAnalyzer: Analyzer[Cell] = new Analyzer[Cell] {
    val principals = (cutBuffer.iterator ++ irreducible.iterator).flatMap { case (c1, c2) => Seq((c1, c2), (c2, c1)) }.toMap
    def irreduciblePairs: IterableOnce[(Cell, Cell)] = irreducible.iterator
    def rootCells = (self.freeWires.iterator ++ principals.keysIterator).toSet
    def getSymbol(c: Cell): Symbol = {
      val sid = getSymId(c)
      reverseSymIds.getOrElse(sid, freeWireLookup.getOrElse(getSymId(c), new Symbol(s"<NoSymbol $sid>")))
    }
    def getConnected(c: Cell, port: Int): (Cell, Int) =
      if(port == -1) principals.get(c).map((_, -1)).orNull else findCellAndPort(c, port)
    def isFreeWire(c: Cell): Boolean = freeWireLookup.contains(getSymId(c))
    override def getPayload(ptr: Long): Any = {
      val sym = getSymbol(ptr)
      if((ptr & TAGMASK) == TAG_UNBOXED) {
        sym.payloadType match {
          case PayloadType.INT => (ptr >>> 32).toInt
        }
      } else {
        val address = ptr + payloadOffset(sym.arity, sym.payloadType)
        sym.payloadType match {
          case PayloadType.INT => Allocator.getInt(address)
          case PayloadType.LABEL => "label@" + Allocator.getLong(address)
          case PayloadType.REF => getProxy(ptr)
        }
      }
    }
  }

  def dispose(): Unit = {
    if(allocator != null) {
      allocator.dispose()
      allocator = null
      if(config.debugMemory) MemoryDebugger.setParent(null)
    }
  }

  def initData(): Unit = {
    cutBuffer.clear()
    irreducible.clear()
    freeWires.clear()
    freeWireLookup.clear()
    //dispose()
    nextLabel = Long.MinValue
    if(allocator == null) {
      allocator = config.newAllocator()
      if(config.debugMemory) {
        MemoryDebugger.setParent(allocator)
        allocator = MemoryDebugger
      }
      singletons.indices.foreach { i =>
        val s = reverseSymIds(i)
        if(s.isSingleton) singletons(i) = newCell(i, s.arity)
      }
    }
    if(config.collectStats) metrics = new ExecutionMetrics
    initialRuleImpls.foreach { rule =>
      val fws = rule.freeWires
      val off = reverseSymIds.size + freeWireLookup.size
      val lhs = newCell(-1, fws.length)
      fws.iterator.zipWithIndex.foreach { case (s, i) =>
        freeWireLookup += ((i+off, s))
        val c = newCell(i+off, 1)
        freeWires += c
        setAux(lhs, i, c, 0)
      }
      val rhs = newCell(-1, 0)
      rule.reduce(lhs, rhs, this)
    }
    if(config.collectStats) metrics = new ExecutionMetrics
  }

  def reduce(): Unit =
    while(!cutBuffer.isEmpty) {
      val (a0, a1) = cutBuffer.pop()
      dispatch.reduce(a0, a1, tailCallDepth, this)
    }

  private final def newCell(symId: Int, arity: Int, pt: PayloadType = PayloadType.VOID): Long = {
    val o = allocator.alloc(cellSize(arity, pt))
    Allocator.putInt(o, mkHeader(symId))
    o
  }

  // ptw methods:

  def addActive(a0: Cell, a1: Cell): Unit = cutBuffer.addOne(a0, a1)

  def addIrreducible(a0: Cell, a1: Cell): Unit = irreducible.addOne(a0, a1)

  def recordStats(steps: Int, cellAllocations: Int, proxyAllocations: Int, cachedCellReuse: Int, singletonUse: Int,
    unboxedCells: Int, loopSave: Int, directTail: Int, singleDispatchTail: Int, labelCreate: Int): Unit =
    metrics.recordStats(steps, cellAllocations, proxyAllocations, cachedCellReuse, singletonUse, unboxedCells,
      loopSave, directTail, singleDispatchTail, labelCreate)

  def recordMetric(metric: String, inc: Int): Unit = metrics.recordMetric(metric, inc)

  def getSingleton(symId: Int): Cell = singletons(symId)

  def allocCell(length: Int): Cell = allocator.alloc(length)
  def freeCell(address: Cell, length: Int): Unit = allocator.free(address, length)
  def allocProxied(length: Int): Cell = allocator.allocProxied(length)
  def freeProxied(address: Cell, length: Int): Unit = allocator.freeProxied(address, length)

  def alloc8(): Long = allocator.alloc8()
  def alloc16(): Long = allocator.alloc16()
  def alloc24(): Long = allocator.alloc24()
  def alloc32(): Long = allocator.alloc32()
  def free8(o: Long): Unit = allocator.free8(o)
  def free16(o: Long): Unit = allocator.free16(o)
  def free24(o: Long): Unit = allocator.free24(o)
  def free32(o: Long): Unit = allocator.free32(o)

  def alloc8p(): Long = allocator.alloc8p()
  def alloc16p(): Long = allocator.alloc16p()
  def alloc24p(): Long = allocator.alloc24p()
  def alloc32p(): Long = allocator.alloc32p()
  def free8p(o: Long): Unit = allocator.free8p(o)
  def free16p(o: Long): Unit = allocator.free16p(o)
  def free24p(o: Long): Unit = allocator.free24p(o)
  def free32p(o: Long): Unit = allocator.free32p(o)

  def getProxyPage(o: Long): AnyRef = allocator.getProxyPage(o)
  def getProxy(o: Long): AnyRef = allocator.getProxy(o)
  def setProxy(o: Long, v: AnyRef): Unit = allocator.setProxy(o, v)

  def newLabel: Long = {
    val r = nextLabel
    nextLabel += 1
    r
  }
}

object Interpreter {
  // Cell layout:
  //   64-bit header
  //   n * 64-bit pointers for arity n
  //   optional 64-bit payload depending on PayloadType
  //
  // Header layout:
  //   LSB                              ...                             MSB
  //   012 3456789abcdef 0123456789abcdef 0123456789abcdef 0123456789abcdef
  //   --------------------------------------------------------------------
  //   110 [29-bit symId                ] [ padding or 32-bit payload     ]
  //
  // Pointer layouts:
  //   LSB                              ...                             MSB
  //   012 3456789abcdef 0123456789abcdef 0123456789abcdef 0123456789abcdef
  //   --------------------------------------------------------------------
  //   000 [ 64-bit aligned address >> 3: pointer to cell (principal)     ]
  //   100 [ 64-bit aligned address >> 3: pointer to aux port             ]
  //   010 [ 29-bit symId               ] [ unboxed 32-bit payload        ]

  final val TAGWIDTH = 3
  final val TAGMASK = 7L
  final val ADDRMASK = -8L
  final val TAG_HEADER = 3
  final val TAG_PRINC_PTR = 0
  final val TAG_AUX_PTR = 1
  final val TAG_UNBOXED = 2

  final val SYMIDMASK = ((1L << 29)-1) << TAGWIDTH

  def showPtr(l: Long, symIds: Map[Int, Symbol] = null): String = {
    var raw = l.toBinaryString
    raw = "0"*(64-raw.length) + raw
    raw = raw.substring(0, 32) + ":" + raw.substring(32, 61) + ":" + raw.substring(61)
    def symStr(sid: Int) =
      if(symIds == null) s"$sid"
      else s"$sid(${symIds.getOrElse(sid, Symbol.NoSymbol).id})"
    val decoded = (l & TAGMASK) match {
      case _ if l == 0L => "NULL"
      case TAG_HEADER =>
        val sid = ((l & SYMIDMASK) >>> TAGWIDTH).toInt
        s"HEADER:${symStr(sid)}:${l >>> 32}"
      case TAG_AUX_PTR => s"AUX_PTR:${l & ADDRMASK}"
      case TAG_PRINC_PTR => s"PRINC_PTR:${l & ADDRMASK}"
      case TAG_UNBOXED =>
        val sid = ((l & SYMIDMASK) >>> TAGWIDTH).toInt
        s"UNBOXED:${symStr(sid)}:${l >>> 32}"
      case tag => s"Invalid-Tag-$tag:$l"
    }
    s"$raw::$decoded"
  }

  def cellSize(arity: Int, pt: PayloadType) = arity*8 + 8 + (if(pt == PayloadType.LABEL) 8 else 0)
  def auxPtrOffset(p: Int): Int = 8 + (p * 8)
  def payloadOffset(arity: Int, pt: PayloadType): Int = if(pt == PayloadType.LABEL) 8 + (arity * 8) else 4
  def mkHeader(sid: Int): Int = (sid << TAGWIDTH) | TAG_HEADER
  def mkUnboxed(sid: Int): Int = (sid << TAGWIDTH) | TAG_UNBOXED

  private def setAux(c: Long, p: Int, c2: Long, p2: Int): Unit = {
    var l = c2 + auxPtrOffset(p2)
    if(p2 >= 0) l |= TAG_AUX_PTR
    Allocator.putLong(c + auxPtrOffset(p), l)
  }

  private def getSymId(ptr: Long) =
    if((ptr & TAGMASK) == TAG_UNBOXED) ((ptr & SYMIDMASK) >>> TAGWIDTH).toInt
    else Allocator.getInt(ptr) >> TAGWIDTH

  private def findCellAndPort(cellAddress: Long, cellPort: Int): (Long, Int) = {
    var ptr = Allocator.getLong(cellAddress + auxPtrOffset(cellPort))
    if((ptr & TAGMASK) != TAG_AUX_PTR) {
      (ptr, -1)
    } else {
      ptr = ptr & ADDRMASK
      var p = -1
      while((Allocator.getInt(ptr - auxPtrOffset(p)) & TAGMASK) != TAG_HEADER)
        p += 1
      (ptr - auxPtrOffset(p), p)
    }
  }

  def canUnbox(sym: Symbol, arity: Int): Boolean =
    arity == 0 && (sym.payloadType == PayloadType.INT || sym.payloadType == PayloadType.VOID)
}

final class CutBuffer(initialSize: Int) {
  private[this] var pairs = new Array[Cell](initialSize*2)
  private[this] var len = 0
  @inline def addOne(c1: Cell, c2: Cell): Unit = {
    if(len == pairs.length)
      pairs = Arrays.copyOf(pairs, pairs.length*2)
    pairs(len) = c1
    pairs(len+1) = c2
    len += 2
  }
  @inline def isEmpty: Boolean = len == 0
  @inline def pop(): (Cell, Cell) = {
    len -= 2
    val c1 = pairs(len)
    val c2 = pairs(len+1)
    (c1, c2)
  }
  def clear(): Unit =
    if(len > 0) {
      pairs = new Array[Cell](initialSize * 2)
      len = 0
    }
  def iterator: Iterator[(Cell, Cell)] = pairs.iterator.take(len).grouped(2).map { case Seq(c1, c2) => (c1, c2) }
}
