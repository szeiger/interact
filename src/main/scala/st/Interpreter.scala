package de.szeiger.interact.st

import de.szeiger.interact.codegen.{LocalClassLoader, ParSupport}
import de.szeiger.interact._
import de.szeiger.interact.ast.{PayloadType, Symbol, Symbols}
import de.szeiger.interact.BitOps._

import java.util.Arrays
import scala.annotation.tailrec
import scala.collection.mutable

abstract class Cell {
  def arity: Int
  def auxCell(p: Int): Cell
  def auxPort(p: Int): Int
  def setAux(p: Int, c2: Cell, p2: Int): Unit
  def reduce(c: Cell, ptw: PerThreadWorker): Unit
}

class InterpreterCell(val symId: Int, val arity: Int) extends Cell {
  private[this] final val auxCells = new Array[Cell](arity)
  private[this] final val auxPorts = new Array[Int](arity)
  final def auxCell(p: Int): Cell = auxCells(p)
  final def auxPort(p: Int): Int = auxPorts(p)
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = { auxCells(p) = c2; auxPorts(p) = p2 }
  final def reduce(c: Cell, ptw: PerThreadWorker): Unit = ptw.reduceInterpreted(this, c.asInstanceOf[InterpreterCell])
  final def getGenericPayload: Any = this match {
    case b: IntBox => b.getValue
    case b: RefBox => b.getValue
    case _ => ()
  }
  private[this] final def auxPortsIterator: Iterator[(Cell, Int)] = (-1 until arity).iterator.map(i => (auxCell(i), auxPort(i)))
  override def toString = s"Cell($symId, $arity, [$getGenericPayload], ${auxPortsIterator.map { w => s"(${if(w._1 == null) "null" else "_"})" }.mkString(", ") })@${System.identityHashCode(this)}"
}
object InterpreterCell {
  def apply(symId: Int, arity: Int, payloadType: PayloadType): InterpreterCell = payloadType match {
    case PayloadType.VOID => new InterpreterCell(symId, arity)
    case PayloadType.INT => new InterpreterCellI(symId, arity)
    case _ => new InterpreterCellR(symId, arity)
  }
}
final class InterpreterCellI(_symId: Int, _arity: Int) extends InterpreterCell(_symId, _arity) with IntBox {
  private[this] final var payload: Int = 0
  def setValue(i: Int) = payload = i
  def getValue: Int = payload
}
final class InterpreterCellR(_symId: Int, _arity: Int) extends InterpreterCell(_symId, _arity) with RefBox {
  private[this] final var payload: AnyRef = null
  def setValue(o: AnyRef) = payload = o
  def getValue: AnyRef = payload
}

final class WireCell(final val sym: Symbol) extends InterpreterCell(0, 1) {
  override def toString = s"WireCell($sym)"
}

abstract class RuleImpl {
  def reduce(c1: Cell, c2: Cell, ptw: PerThreadWorker): Unit
}

final class InterpretedRuleImpl(s1id: Int, protoCells: Array[Int], freeWiresPorts: Array[Int], connections: Array[Long],
    embeddedComps: Array[PayloadComputation], condComp: PayloadComputation, next: RuleImpl, sym1: Symbol, sym2: Symbol) extends RuleImpl {

  override def toString = s"InterpretedRuleImpl($sym1 <-> $sym2)"

  private[this] def delay(nanos: Int): Unit = {
    val end = System.nanoTime() + nanos
    while(System.nanoTime() < end) Thread.onSpinWait()
  }

  def reduce(_c1: Cell, _c2: Cell, ptw: PerThreadWorker): Unit = try {
    val (c1, c2) = {
      val ic1 = _c1.asInstanceOf[InterpreterCell]
      val ic2 = _c2.asInstanceOf[InterpreterCell]
      if(ic1.symId == s1id) (ic1, ic2) else (ic2, ic1)
    }

    if(condComp != null) {
      val condArgs = condComp.embArgs
      var i = 0
      val args = new Array[Any](condArgs.length)
      while(i < condArgs.length) {
        args(i) = condArgs(i) match {
          case EmbArg.Left => c1.getGenericPayload
          case EmbArg.Right => c2.getGenericPayload
          case EmbArg.Const(v) => v
        }
        i += 1
      }
      val b = condComp.invoke(args).asInstanceOf[Boolean]
      if(!b) return next.reduce(_c1, _c2, ptw)
    }

    val cells = ptw.tempCells
    //delay(20)
    var i = 0
    while(i < protoCells.length) {
      val pc = protoCells(i)
      val sid = short0(pc)
      val ari = byte2(pc)
      val pt = byte3(pc)
      cells(i) = InterpreterCell(sid, ari, new PayloadType(pt))
      i += 1
    }

    if(embeddedComps != null) {
      var j = 0
      while(j < embeddedComps.length) {
        val embeddedComp = embeddedComps(j)
        val embeddedArgs = embeddedComp.embArgs
        val args = new Array[Any](embeddedArgs.length)
        i = 0
        while(i < embeddedArgs.length) {
          args(i) = embeddedArgs(i) match {
            case EmbArg.Left => c1.getGenericPayload
            case EmbArg.Right => c2.getGenericPayload
            case EmbArg.Cell(n) => cells(n)
            case EmbArg.Const(v) => v
          }
          i += 1
        }
        embeddedComp.invoke(args)
        j += 1
      }
    }

    @inline def cccells(i: Int): Cell = if(i < c1.arity) c1.auxCell(i) else c2.auxCell(i - c1.arity)
    @inline def ccports(i: Int): Int = if(i < c1.arity) c1.auxPort(i) else c2.auxPort(i - c1.arity)

    // Connect new cell to cut wire
    @inline def connectNewToFree(ct1: Int, p1: Int, ct2: Int): Unit = {
      val cc1 = cells(ct1)
      val cc2 = cccells(ct2)
      val p2 = ccports(ct2)
      if(p1 >= 0) cc1.setAux(p1, cc2, p2)
      if(p2 >= 0) cc2.setAux(p2, cc1, p1)
      if((p1 & p2) < 0) ptw.createCut(cc1, cc2)
    }

    @inline def connectFreeToFree(ct1: Int, ct2: Int): Unit = {
      val cc1 = cccells(ct1)
      val p1 = ccports(ct1)
      val cc2 = cccells(ct2)
      val p2 = ccports(ct2)
      if(p1 >= 0) cc1.setAux(p1, cc2, p2)
      if(p2 >= 0) cc2.setAux(p2, cc1, p1)
      if((p1 & p2) < 0) ptw.createCut(cc1, cc2)
    }

    i = 0
    while(i < freeWiresPorts.length) {
      val fwp = freeWiresPorts(i)
      val fw = short0(fwp)
      if(fw >= 0) connectNewToFree(fw, short1(fwp), i)
      else if(i < -1-fw) connectFreeToFree(i, -1-fw)
      i += 1
    }

    i = 0
    while(i < connections.length) {
      val conn = connections(i)
      val c1 = cells(LongBitOps.short0(conn))
      val p1 = LongBitOps.short1(conn)
      val c2 = cells(LongBitOps.short2(conn))
      val p2 = LongBitOps.short3(conn)
      if(p1 >= 0) c1.setAux(p1, c2, p2)
      if(p2 >= 0) c2.setAux(p2, c1, p1)
      if((p1 & p2) < 0) ptw.createCut(c1, c2)
      i += 1
    }

    if(ptw.metrics != null) ptw.metrics.recordStats(protoCells.length)
  } catch { case ex: Exception =>
    throw new RuntimeException(s"Error evaluating rule $this: $ex", ex)
  }
}

final class Interpreter(globals: Symbols, rules: scala.collection.Map[RuleKey, RulePlan],
  config: BackendConfig, initialRules: Iterable[InitialPlan]) extends BaseInterpreter { self =>

  private[this] final val allSymbols = globals.symbols
  private[this] final val symIds = mutable.HashMap.from[Symbol, Int](allSymbols.zipWithIndex.map { case (s, i) => (s, i+1) })
  private[this] final val reverseSymIds = symIds.iterator.map { case (k, v) => (v, k) }.toMap
  private[this] final val symBits = Integer.numberOfTrailingZeros(Integer.highestOneBit(symIds.size))+1
  final val (ruleImpls, maxRuleCells, initialRuleImpls, classToSym) = createRuleImpls()
  final val cutBuffer, irreducible = new CutBuffer(16)
  final val freeWires = mutable.HashSet.empty[Cell]
  private[this] var metrics: ExecutionMetrics = _

  def getMetrics: ExecutionMetrics = metrics

  def getSymbol(c: Cell): Symbol = c match {
    case c: WireCell => c.sym
    case c: InterpreterCell if c.symId == 0 => Symbol.NoSymbol
    case c: InterpreterCell => reverseSymIds(c.symId)
    case c => classToSym.getOrElse(c.getClass, Symbol.NoSymbol)
  }

  def getAnalyzer: Analyzer[Cell] = new Analyzer[Cell] {
    def irreduciblePairs: IterableOnce[(Cell, Cell)] = irreducible.iterator
    val principals = mutable.HashMap.empty[Cell, Cell]
    (cutBuffer.iterator ++ irreducible.iterator).foreach { case (c1, c2) =>
      principals.put(c1, c2)
      principals.put(c2, c1)
    }
    def rootCells = (self.freeWires.iterator ++ (cutBuffer.iterator ++ principals.iterator).flatMap { case (c1, c2) => Seq(c1, c2) }).filter(_ != null).toSet
    def getSymbol(c: Cell): Symbol = self.getSymbol(c)
    def getPayload(c: Cell): Any = c match {
      case c: IntBox => c.getValue
      case c: RefBox => c.getValue
      case c => "???"
    }
    def getConnected(c: Cell, port: Int): (Cell, Int) =
      if(port == -1) principals.get(c).map((_, -1)).getOrElse(null)
      else (c.auxCell(port), c.auxPort(port))
    def isFreeWire(c: Cell): Boolean = c.isInstanceOf[WireCell]
  }

  def initData(): Unit = {
    cutBuffer.clear()
    irreducible.clear()
    freeWires.clear()
    val w = new PerThreadWorker(this, if(config.collectStats) new ExecutionMetrics else null)
    initialRuleImpls.foreach { case (freeSyms, rule) =>
      val free = freeSyms.map(new WireCell(_))
      freeWires.addAll(free)
      val lhs = InterpreterCell(0, freeWires.size, PayloadType.VOID)
      free.zipWithIndex.foreach { case (c, p) => lhs.setAux(p, c, 0) }
      rule.reduce(lhs, InterpreterCell(0, 0, PayloadType.VOID), w)
    }
    w.flushNext()
  }

  def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)
  def createTempCells(): Array[Cell] = new Array[Cell](maxRuleCells)

  def createInterpretedRuleImpl(sym1Id: Int, r: GenericRulePlan, b: BranchPlan, next: Option[RuleImpl]): RuleImpl = {
    val bp = new PackedBranchPlan(b, r)
    val pcs = b.cells.iterator.map(s => intOfShortByteByte(getSymbolId(s), s.arity, s.payloadType.value)).toArray
    new InterpretedRuleImpl(sym1Id, pcs, bp.freeWiresPacked, bp.connectionsPackedLong,
      if(b.payloadComps.isEmpty) null else b.payloadComps.toArray, b.cond.orNull, next.orNull, r.sym1, r.sym2)
  }

  def createRuleImpls(): (Array[RuleImpl], Int, Vector[(Vector[Symbol], RuleImpl)], Map[Class[_], Symbol]) = {
    if(config.compile) {
      val cg = new CodeGen("generated", new LocalClassLoader, config)
      val (initial, classToSym) = cg.compile(rules, initialRules, globals)
      (null, 0, initial, classToSym)
    } else {
      val ris = new Array[RuleImpl](1 << (symBits << 1))
      val maxC = new ParSupport.AtomicCounter
      val classToSymbol = Map.newBuilder[Class[_], Symbol]
      ParSupport.foreach(rules.values, config.compilerParallelism) { g =>
        maxC.max(g.maxCells)
        val sym1Id = getSymbolId(g.sym1)
        val ri = g.branches.foldRight(null: RuleImpl) { case (b, z) => createInterpretedRuleImpl(sym1Id, g, b, Option(z)) }
        ris(mkRuleKey(sym1Id, getSymbolId(g.sym2))) = ri
      }
      val initial = Vector.newBuilder[(Vector[Symbol], RuleImpl)]
      initialRules.zipWithIndex.foreach { case (ip, i) =>
        maxC.max(ip.maxCells)
        initial += ((ip.free, createInterpretedRuleImpl(0, ip, ip.branch, None)))
      }
      (ris, maxC.get, initial.result(), classToSymbol.result())
    }
  }

  @inline def mkRuleKey(c1: InterpreterCell, c2: InterpreterCell): Int = mkRuleKey(c1.symId, c2.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  // Used by the debugger
  def getRuleImpl(c1: Cell, c2: Cell): RuleImpl = ruleImpls(mkRuleKey(c1.asInstanceOf[InterpreterCell], c2.asInstanceOf[InterpreterCell]))
  def reduce1(c1: Cell, c2: Cell): Unit = {
    val w = new PerThreadWorker(this, null)
    w.setNext(c1, c2)
    w.processNext()
    val (d1, d2) = w.getNext
    if(d1 != null) cutBuffer.addOne(d1, d2)
  }

  def reduce(): Unit = {
    this.metrics = if(config.collectStats) new ExecutionMetrics else null
    val w = new PerThreadWorker(this, metrics)
    while(cutBuffer.nonEmpty) {
      val (c1, c2) = cutBuffer.pop()
      w.setNext(c1, c2)
      w.processAll()
    }
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
  @inline def nonEmpty: Boolean = len != 0
  @inline def pop(): (Cell, Cell) = {
    len -= 2
    val c1 = pairs(len)
    val c2 = pairs(len+1)
    pairs(len) = null
    pairs(len+1) = null
    (c1, c2)
  }
  def clear(): Unit =
    if(len > 0) {
      new Array[Cell](initialSize * 2)
      len = 0
    }
  def iterator: Iterator[(Cell, Cell)] = pairs.iterator.take(len*2).grouped(2).map { case Seq(c1, c2) => (c1, c2) }
}

final class PerThreadWorker(final val inter: Interpreter, val metrics: ExecutionMetrics) {
  final val tempCells = inter.createTempCells()
  private[this] final var nextCut1, nextCut2: Cell = _

  def createCut(c1: Cell, c2: Cell): Unit = {
    if(nextCut1 == null) { nextCut1 = c1; nextCut2 = c2 }
    else inter.cutBuffer.addOne(c1, c2)
  }

  def setNext(c1: Cell, c2: Cell): Unit = {
    this.nextCut1 = c1
    this.nextCut2 = c2
  }

  def flushNext(): Unit = {
    if(nextCut1 != null) {
      inter.cutBuffer.addOne(nextCut1, nextCut2)
      nextCut1 = null
      nextCut2 = null
    }
  }

  def getNext: (Cell, Cell) = (nextCut1, nextCut2)

  def reduceInterpreted(c1: InterpreterCell, c2: InterpreterCell): Unit = {
    val ri = inter.ruleImpls(inter.mkRuleKey(c1, c2))
    if(ri != null) ri.reduce(c1, c2, this)
    else irreducible(c1, c2)
  }

  def irreducible(c1: Cell, c2: Cell): Unit = inter.irreducible.addOne(c1, c2)

  def recordStats(cellAllocations: Int, cachedCellReuse: Int, singletonUse: Int, loopSave: Int, labelCreate: Int): Unit =
    metrics.recordStats(cellAllocations, cachedCellReuse, singletonUse, loopSave, labelCreate)
  def recordMetric(metric: String, inc: Int): Unit = metrics.recordMetric(metric, inc)

  def processNext(): Unit = {
    val c1 = nextCut1
    val c2 = nextCut2
    nextCut1 = null
    nextCut2 = null
    c1.reduce(c2, this)
  }

  @tailrec
  def processAll(): Unit = {
    processNext()
    if(nextCut1 != null) processAll()
  }
}
