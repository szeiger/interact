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
      val sid = Allocator.symId(c)
      reverseSymIds.getOrElse(sid, freeWireLookup.getOrElse(Allocator.symId(c), new Symbol(s"<NoSymbol $sid>")))
    }
    def getConnected(c: Cell, port: Int): (Cell, Int) =
      if(port == -1) principals.get(c).map((_, -1)).orNull else Allocator.findCellAndPort(Allocator.auxCP(c, port))
    def isFreeWire(c: Cell): Boolean = freeWireLookup.contains(Allocator.symId(c))
    def isSharedSingleton(c: Cell): Boolean = c.getClass.getField("singleton") != null
    override def getPayload(c: Cell): Any = {
      val sym = getSymbol(c)
      val address = c + Allocator.payloadOffset(sym.arity, sym.payloadType)
      sym.payloadType match {
        case PayloadType.INT => Allocator.getInt(address)
        case PayloadType.LABEL => "label@" + Allocator.getLong(address)
        case PayloadType.REF => getProxy(c)
      }
    }
  }

  def dispose(): Unit = {
    if(allocator != null) {
      //Arrays.fill(singletons, 0L)
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
        if(s.isSingleton) singletons(i) = allocator.newCell(i, s.arity)
      }
    }
    if(config.collectStats) metrics = new ExecutionMetrics
    initialRuleImpls.foreach { rule =>
      val fws = rule.freeWires
      val off = reverseSymIds.size + freeWireLookup.size
      val lhs = allocator.newCell(-1, fws.length)
      fws.iterator.zipWithIndex.foreach { case (s, i) =>
        freeWireLookup += ((i+off, s))
        val c = allocator.newCell(i+off, 1)
        freeWires += c
        Allocator.setAux(lhs, i, c, 0)
      }
      val rhs = allocator.newCell(-1, 0)
      rule.reduce(lhs, rhs, this)
    }
    if(config.collectStats) metrics = new ExecutionMetrics
  }

  def reduce(): Unit =
    while(!cutBuffer.isEmpty) {
      val (a0, a1) = cutBuffer.pop()
      dispatch.reduce(a0, a1, tailCallDepth, this)
    }

  // ptw methods:

  def addActive(a0: Cell, a1: Cell): Unit = cutBuffer.addOne(a0, a1)

  def addIrreducible(a0: Cell, a1: Cell): Unit = irreducible.addOne(a0, a1)

  def recordStats(steps: Int, cellAllocations: Int, proxyAllocations: Int, cachedCellReuse: Int, singletonUse: Int,
    loopSave: Int, directTail: Int, singleDispatchTail: Int, labelCreate: Int): Unit =
    metrics.recordStats(steps, cellAllocations, proxyAllocations, cachedCellReuse, singletonUse, loopSave, directTail, singleDispatchTail, labelCreate)

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
