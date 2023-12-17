package de.szeiger.interact.st

import de.szeiger.interact.codegen.{LocalClassLoader, ParSupport}
import de.szeiger.interact._
import de.szeiger.interact.ast.{CheckedRule, EmbeddedExpr, PayloadType, Symbol, Symbols}
import de.szeiger.interact.mt.BitOps._

import java.util.Arrays
import scala.annotation.{switch, tailrec}
import scala.collection.mutable

abstract class Cell(final var symId: Int, _pcell: Cell, _pport: Int) {
  final var pcell: Cell = _pcell
  final var pport: Int = _pport

  def arity: Int
  def auxCell(p: Int): Cell
  def auxPort(p: Int): Int
  def setAux(p: Int, c2: Cell, p2: Int): Unit
  def setCell(p: Int, c2: Cell, p2: Int): Unit
  def getCell(p: Int): Cell
  def getPort(p: Int): Int
  def getGenericPayload: Any
  def setGenericPayload(v: Any): Unit

  final def allPorts: Iterator[(Cell, Int)] = (-1 until arity).iterator.map(i => (getCell(i), getPort(i)))
  override def toString = s"Cell($symId, $arity, [$getGenericPayload], ${allPorts.map { w => s"(${if(w._1 == null) "null" else "_"})" }.mkString(", ") })@${System.identityHashCode(this)}"
}

trait IntCell extends IntBox {
  private[this] final var payload: Int = 0
  def setValue(i: Int) = payload = i
  def getValue: Int = payload
  def setGenericPayload(v: Any): Unit = payload = v.asInstanceOf[Int]
  def getGenericPayload: Any = payload
}
trait RefCell extends RefBox {
  private[this] final var payload: AnyRef = null
  def setValue(o: AnyRef) = payload = o
  def getValue: AnyRef = payload
  def setGenericPayload(v: Any): Unit = payload = v.asInstanceOf[AnyRef]
  def getGenericPayload: Any = payload
}
trait VoidCell {
  def getValue: Unit = ()
  def setGenericPayload(v: Any): Unit = ()
  def getGenericPayload: Any = ()
}

abstract class Cell0(_symId: Int, _pcell: Cell, _pport: Int) extends Cell(_symId, _pcell, _pport) {
  final def arity: Int = 0
  final def auxCell(p: Int): Cell = null
  final def auxPort(p: Int): Int = 0
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = ()
  final def setCell(p: Int, c2: Cell, p2: Int): Unit = { pcell = c2; pport = p2 }
  final def getCell(p: Int): Cell = pcell
  final def getPort(p: Int): Int = pport
}
class Cell0V(_symId: Int, _pcell: Cell, _pport: Int) extends Cell0(_symId, _pcell, _pport) with VoidCell {
  def this(_symId: Int) = this(_symId, null, 0)
}
class Cell0I(_symId: Int, _pcell: Cell, _pport: Int) extends Cell0(_symId, _pcell, _pport) with IntCell {
  def this(_symId: Int) = this(_symId, null, 0)
}
class Cell0L(_symId: Int, _pcell: Cell, _pport: Int) extends Cell0(_symId, _pcell, _pport) with RefCell {
  def this(_symId: Int) = this(_symId, null, 0)
}

abstract class Cell1(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int) extends Cell(_symId, _pcell, _pport) {
  final var acell0: Cell = _acell0
  final var aport0: Int = _aport0
  final def arity: Int = 1
  final def auxCell(p: Int): Cell = acell0
  final def auxPort(p: Int): Int = aport0
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = { acell0 = c2; aport0 = p2 }
  final def setCell(p: Int, c2: Cell, p2: Int): Unit = if(p == 0) { acell0 = c2; aport0 = p2 } else { pcell = c2; pport = p2 }
  final def getCell(p: Int): Cell = if(p == 0) acell0 else pcell
  final def getPort(p: Int): Int = if(p == 0) aport0 else pport
}
class Cell1V(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int) extends Cell1(_symId, _pcell, _pport, _acell0, _aport0) with VoidCell {
  def this(_symId: Int) = this(_symId, null, 0, null, 0)
}
class Cell1I(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int) extends Cell1(_symId, _pcell, _pport, _acell0, _aport0) with IntCell {
  def this(_symId: Int) = this(_symId, null, 0, null, 0)
}
class Cell1L(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int) extends Cell1(_symId, _pcell, _pport, _acell0, _aport0) with RefCell {
  def this(_symId: Int) = this(_symId, null, 0, null, 0)
}

abstract class Cell2(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int, _acell1: Cell, _aport1: Int) extends Cell(_symId, _pcell, _pport) {
  final var acell0: Cell = _acell0
  final var aport0: Int = _aport0
  final var acell1: Cell = _acell1
  final var aport1: Int = _aport1
  final def arity: Int = 2
  final def auxCell(p: Int): Cell = if(p == 0) acell0 else acell1
  final def auxPort(p: Int): Int = if(p == 0) aport0 else aport1
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = if(p == 0) { acell0 = c2; aport0 = p2 } else { acell1 = c2; aport1 = p2 }
  final def setCell(p: Int, c2: Cell, p2: Int): Unit = (p: @switch) match {
    case 0 => acell0 = c2; aport0 = p2
    case 1 => acell1 = c2; aport1 = p2
    case _ => pcell = c2; pport = p2
  }
  final def getCell(p: Int): Cell = (p: @switch) match {
    case 0 => acell0
    case 1 => acell1
    case _ => pcell
  }
  final def getPort(p: Int): Int = (p: @switch) match {
    case 0 => aport0
    case 1 => aport1
    case _ => pport
  }
}
class Cell2V(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int, _acell1: Cell, _aport1: Int) extends Cell2(_symId, _pcell, _pport, _acell0, _aport0, _acell1, _aport1) with VoidCell {
  def this(_symId: Int) = this(_symId, null, 0, null, 0, null, 0)
}
class Cell2I(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int, _acell1: Cell, _aport1: Int) extends Cell2(_symId, _pcell, _pport, _acell0, _aport0, _acell1, _aport1) with IntCell {
  def this(_symId: Int) = this(_symId, null, 0, null, 0, null, 0)
}
class Cell2L(_symId: Int, _pcell: Cell, _pport: Int, _acell0: Cell, _aport0: Int, _acell1: Cell, _aport1: Int) extends Cell2(_symId, _pcell, _pport, _acell0, _aport0, _acell1, _aport1) with RefCell {
  def this(_symId: Int) = this(_symId, null, 0, null, 0, null, 0)
}

abstract class CellN(_symId: Int, val arity: Int, _pcell: Cell, _pport: Int) extends Cell(_symId, _pcell, _pport) {
  def this(_symId: Int, _arity: Int) = this(_symId, _arity, null, 0)
  private[this] final val auxCells = new Array[Cell](arity)
  private[this] final val auxPorts = new Array[Int](arity)
  final def auxCell(p: Int): Cell = auxCells(p)
  final def auxPort(p: Int): Int = auxPorts(p)
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = { auxCells(p) = c2; auxPorts(p) = p2 }
  final def setCell(p: Int, c2: Cell, p2: Int): Unit =
    if(p < 0) { pcell = c2; pport = p2 } else { auxCells(p) = c2; auxPorts(p) = p2 }
  final def getCell(p: Int): Cell = if(p < 0) pcell else auxCells(p)
  final def getPort(p: Int): Int = if(p < 0) pport else auxPorts(p)
}
class CellNV(_symId: Int, _arity: Int, _pcell: Cell, _pport: Int) extends CellN(_symId, _arity, _pcell, _pport) with VoidCell {
  def this(_symId: Int, _arity: Int) = this(_symId, _arity, null, 0)
}
class CellNI(_symId: Int, _arity: Int, _pcell: Cell, _pport: Int) extends CellN(_symId, _arity, _pcell, _pport) with IntCell {
  def this(_symId: Int, _arity: Int) = this(_symId, _arity, null, 0)
}
class CellNL(_symId: Int, _arity: Int, _pcell: Cell, _pport: Int) extends CellN(_symId, _arity, _pcell, _pport) with RefCell {
  def this(_symId: Int, _arity: Int) = this(_symId, _arity, null, 0)
}

object Cells {
  def mk(symId: Int, arity: Int, payloadKind: Int): Cell = (payloadKind: @switch) match {
    case VOID0 => new Cell0V(symId)
    case VOID1 => new Cell1V(symId)
    case VOID2 => new Cell2V(symId)
    case VOIDN => new CellNV(symId, arity)
    case INT0  => new Cell0I(symId)
    case INT1  => new Cell1I(symId)
    case INT2  => new Cell2I(symId)
    case INTN  => new CellNI(symId, arity)
    case REF0 | LABEL0 => new Cell0L(symId)
    case REF1 | LABEL1 => new Cell1L(symId)
    case REF2 | LABEL2 => new Cell2L(symId)
    case REFN | LABELN => new CellNL(symId, arity)
  }

  final val VOID0  = 0 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.VOID.value
  final val VOID1  = 1 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.VOID.value
  final val VOID2  = 2 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.VOID.value
  final val VOIDN  = 3 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.VOID.value
  final val INT0   = 0 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.INT.value
  final val INT1   = 1 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.INT.value
  final val INT2   = 2 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.INT.value
  final val INTN   = 3 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.INT.value
  final val REF0   = 0 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.REF.value
  final val REF1   = 1 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.REF.value
  final val REF2   = 2 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.REF.value
  final val REFN   = 3 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.REF.value
  final val LABEL0 = 0 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.LABEL.value
  final val LABEL1 = 1 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.LABEL.value
  final val LABEL2 = 2 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.LABEL.value
  final val LABELN = 3 * PayloadType.PAYLOAD_TYPES_COUNT + PayloadType.LABEL.value

  def cellKind(arity: Int, payloadType: PayloadType): Int = payloadType.value + math.min(arity, 3) * PayloadType.PAYLOAD_TYPES_COUNT
}

class WireCell(final val sym: Symbol, _symId: Int) extends Cell1V(0) {
  override def toString = s"WireCell($sym, $symId)"
}

abstract class RuleImpl {
  var rule: GenericRule = _
  def reduce(cut: Cell, ptw: PerThreadWorker): Unit
  def cellAllocationCount: Int
}

final class InterpretedRuleImpl(s1id: Int, protoCells: Array[Int], freeWiresPorts: Array[Int], connections: Array[Int],
    assigners: Array[PayloadAssigner], embeddedComps: Array[EmbeddedComputation[Int]], embeddedArgss: Array[scala.collection.Seq[Int]],
    condComp: EmbeddedComputation[Int], condArgs: scala.collection.Seq[Int], next: RuleImpl) extends RuleImpl {
  override def toString = rule.toString

  private[this] def delay(nanos: Int): Unit = {
    val end = System.nanoTime() + nanos
    while(System.nanoTime() < end) Thread.onSpinWait()
  }

  def reduce(cell: Cell, ptw: PerThreadWorker): Unit = {
    val (c1, c2) = if(cell.symId == s1id) (cell, cell.pcell) else (cell.pcell, cell)

    if(condComp != null) {
      var i = 0
      val args = new Array[Any](condArgs.length)
      while(i < condArgs.length) {
        args(i) = condArgs(i) match {
          case -1 => c1.getGenericPayload
          case -2 => c2.getGenericPayload
        }
        i += 1
      }
      val b = condComp.invoke(args).asInstanceOf[Boolean]
      if(!b) return next.reduce(cell, ptw)
    }

    val cells = ptw.tempCells
    //delay(20)
    var i = 0
    while(i < protoCells.length) {
      val pc = protoCells(i)
      val sid = short0(pc)
      val ari = byte2(pc)
      val kind = byte3(pc)
      cells(i) = Cells.mk(sid, ari, kind)
      i += 1
    }

    i = 0
    while(i < assigners.length) {
      val ass = assigners(i)
      ass(c1, c2, cells(ass.cellIdx))
      i += 1
    }
    if(embeddedComps != null) {
      var j = 0
      while(j < embeddedComps.length) {
        val embeddedComp = embeddedComps(j)
        val embeddedArgs = embeddedArgss(j)
        val args = new Array[Any](embeddedArgs.length)
        i = 0
        while(i < embeddedArgs.length) {
          args(i) = embeddedArgs(i) match {
            case -1 => c1.getGenericPayload
            case -2 => c2.getGenericPayload
            case n => cells(n)
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
      cc1.setCell(p1, cc2, p2)
      cc2.setCell(p2, cc1, p1)
      if((p1 & p2) < 0) ptw.createCut(cc1)
    }

    @inline def connectFreeToFree(ct1: Int, ct2: Int): Unit = {
      val cc1 = cccells(ct1)
      val p1 = ccports(ct1)
      val cc2 = cccells(ct2)
      val p2 = ccports(ct2)
      cc1.setCell(p1, cc2, p2)
      cc2.setCell(p2, cc1, p1)
      if((p1 & p2) < 0) ptw.createCut(cc1)
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
      val c1 = cells(byte0(conn))
      val p1 = byte1(conn)
      val c2 = cells(byte2(conn))
      val p2 = byte3(conn)
      c1.setCell(p1, c2, p2)
      c2.setCell(p2, c1, p1)
      if((p1 & p2) < 0) ptw.createCut(c1)
      i += 1
    }
  }

  def cellAllocationCount: Int = protoCells.length
}

final class Interpreter(globals: Symbols, rules: Iterable[CheckedRule], compile: Boolean,
  debugLog: Boolean, debugBytecode: Boolean, val collectStats: Boolean) extends BaseInterpreter with SymbolIdLookup { self =>
  final val scope: Analyzer[Cell] = new Analyzer[Cell] {
    def createCell(sym: Symbol, emb: Option[EmbeddedExpr]): Cell =
      if(sym.isCons) Cells.mk(getSymbolId(sym), sym.arity, Cells.cellKind(sym.arity, sym.payloadType)) else new WireCell(sym, 0)
    def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit = {
      c1.setCell(p1, c2, p2)
      c2.setCell(p2, c1, p1)
    }
    def getSymbol(c: Cell): Symbol = c match {
      case c: WireCell => c.sym
      case c => reverseSymIds(c.symId)
    }
    def getPayload(c: Cell): Any = c.getGenericPayload
    def getConnected(c: Cell, port: Int): (Cell, Int) = (c.getCell(port), c.getPort(port))
    def isFreeWire(c: Cell): Boolean = c.isInstanceOf[WireCell]
  }
  private[this] final val allSymbols = globals.symbols
  private[this] final val symIds = mutable.HashMap.from[Symbol, Int](allSymbols.zipWithIndex.map { case (s, i) => (s, i+1) })
  private[this] final val reverseSymIds = symIds.iterator.map { case (k, v) => (v, k) }.toMap
  private[this] final val symBits = Integer.numberOfTrailingZeros(Integer.highestOneBit(symIds.size))+1
  final val (ruleImpls, maxRuleCells, maxArity) = createRuleImpls()

  def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)
  def getSymbolId(name: String): Int = getSymbolId(globals(name))
  def createTempCells(): Array[Cell] = new Array[Cell](maxRuleCells)
  def createCutCache(): (Array[Cell], Array[Int]) = (new Array[Cell](maxArity*2), new Array[Int](maxArity*2))

  def createInterpretedRuleImpl(g: GenericRule, b: GenericRuleBranch, next: Option[RuleImpl]): RuleImpl = {
    val pcs = b.cells.map(s => intOfShortByteByte(getSymbolId(s), s.arity, Cells.cellKind(s.arity, s.payloadType)))
    val embArgs = b.embeddedComps.map(_.argIndices)
    val condArgs = b.condition.map(_.argIndices)
    new InterpretedRuleImpl(getSymbolId(g.sym1), pcs, b.freeWiresPacked, b.connectionsPacked, b.assigners,
      if(b.embeddedComps.isEmpty) null else b.embeddedComps.toArray, if(embArgs.isEmpty) null else embArgs.toArray,
      b.condition.orNull, condArgs.orNull, next.orNull)
  }

  def createRuleImpls(): (Array[RuleImpl], Int, Int) = {
    val (cl, codeGen) =
      if(compile) (new LocalClassLoader(), new CodeGen("de/szeiger/interact/st3/gen", debugBytecode))
      else (null, null)
    val ris = new Array[RuleImpl](1 << (symBits << 1))
    val maxC, maxA = new ParSupport.AtomicCounter
    ParSupport.foreach(rules) { cr =>
      val g = GenericRule(getClass.getClassLoader, cr)
      if(debugLog) g.log()
      maxC.max(g.maxCells)
      maxA.max(g.arity1)
      maxA.max(g.arity2)
      val ri =
        if(compile) codeGen.compile(g, cl)(this)
        else g.branches.foldRight(null: RuleImpl) { case (b, z) => createInterpretedRuleImpl(g, b, Option(z)) }
      ri.rule = g
      ris(mkRuleKey(getSymbolId(g.sym1), getSymbolId(g.sym2))) = ri
    }
    (ris, maxC.get, maxA.get)
  }

  @inline def mkRuleKey(c: Cell): Int = mkRuleKey(c.symId, c.pcell.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  def detectInitialCuts: CutBuffer = {
    val detected = mutable.HashSet.empty[Cell]
    val buf = new CutBuffer(16)
    scope.reachableCells.foreach { c =>
      if(!scope.isFreeWire(c)) {
        val ri = ruleImpls(mkRuleKey(c))
        if(ri != null) {
          if(c.pport < 0 && c.pcell.pport < 0 && !detected.contains(c.pcell)) {
            detected.addOne(c)
            buf.addOne(c, ri)
          }
        }
      }
    }
    buf
  }

  // Used by the debugger
  def getRuleImpl(c: Cell): RuleImpl = ruleImpls(mkRuleKey(c))
  def reduce1(c: Cell): Unit = {
    val w = new PerThreadWorker(this) {
      protected[this] override def enqueueCut(c: Cell, ri: RuleImpl): Unit = ()
    }
    w.setNext(c, getRuleImpl(c))
    w.processNext()
  }

  def reduce(): Int = {
    val initial = detectInitialCuts
    val w = new PerThreadWorker(this) {
      protected[this] override def enqueueCut(c: Cell, ri: RuleImpl): Unit = initial.addOne(c, ri)
    }
    while(initial.nonEmpty) {
      val (wr, ri) = initial.pop()
      w.setNext(wr, ri)
      w.processAll()
    }
    if(collectStats)
      println(s"Total steps: ${w.steps}, allocated cells: ${w.cellAllocations}")
    w.steps
  }
}

final class CutBuffer(initialSize: Int) {
  private[this] var wrs = new Array[Cell](initialSize)
  private[this] var ris = new Array[RuleImpl](initialSize)
  private[this] var len = 0
  @inline def addOne(wr: Cell, ri: RuleImpl): Unit = {
    if(len == wrs.length) {
      wrs = Arrays.copyOf(wrs, wrs.length*2)
      ris = Arrays.copyOf(ris, ris.length*2)
    }
    wrs(len) = wr
    ris(len) = ri
    len += 1
  }
  @inline def nonEmpty: Boolean = len != 0
  @inline def pop(): (Cell, RuleImpl) = {
    len -= 1
    val wr = wrs(len)
    val ri = ris(len)
    wrs(len) = null
    (wr, ri)
  }
}

abstract class PerThreadWorker(final val inter: Interpreter) {
  final val tempCells = inter.createTempCells()
  final val (cutCacheCells, cutCachePorts) = inter.createCutCache()
  private[this] final var nextCut: Cell = _
  private[this] final var nextRule: RuleImpl = _
  private[this] final val collectStats = inter.collectStats
  var steps, cellAllocations = 0

  protected[this] def enqueueCut(c: Cell, ri: RuleImpl): Unit

  final def createCut(c: Cell): Unit = {
    val ri = inter.ruleImpls(inter.mkRuleKey(c))
    if(ri != null) {
      if(nextCut == null) { nextCut = c; nextRule = ri }
      else enqueueCut(c, ri)
    }
  }

  final def setNext(c: Cell, ri: RuleImpl): Unit = {
    this.nextCut = c
    this.nextRule = ri
  }

  final def processNext(): Unit = {
    val c = nextCut
    val ri = nextRule
    nextCut = null
    ri.reduce(c, this)
    if(collectStats) {
      steps += 1
      cellAllocations += ri.cellAllocationCount
    }
  }

  @tailrec
  final def processAll(): Unit = {
    processNext()
    if(nextCut != null) processAll()
  }
}
