package de.szeiger.interact.st

import de.szeiger.interact.codegen.{LocalClassLoader, ParSupport}
import de.szeiger.interact._
import de.szeiger.interact.ast.{CheckedRule, EmbeddedExpr, PayloadType, Symbol, Symbols}
import de.szeiger.interact.codegen.SymbolIdLookup
import de.szeiger.interact.mt.BitOps._

import java.util.Arrays
import scala.annotation.{switch, tailrec}
import scala.collection.mutable

abstract class Cell(final var symId: Int) {
  def arity: Int
  def auxCell(p: Int): Cell
  def auxPort(p: Int): Int
  def setAux(p: Int, c2: Cell, p2: Int): Unit
  def getGenericPayload: Any
  def setGenericPayload(v: Any): Unit

  final def auxPortsIterator: Iterator[(Cell, Int)] = (-1 until arity).iterator.map(i => (auxCell(i), auxPort(i)))
  override def toString = s"Cell($symId, $arity, [$getGenericPayload], ${auxPortsIterator.map { w => s"(${if(w._1 == null) "null" else "_"})" }.mkString(", ") })@${System.identityHashCode(this)}"
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

abstract class Cell0(_symId: Int) extends Cell(_symId) {
  final def arity: Int = 0
  final def auxCell(p: Int): Cell = null
  final def auxPort(p: Int): Int = 0
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = ()
}
class Cell0V(_symId: Int) extends Cell0(_symId) with VoidCell
class Cell0I(_symId: Int) extends Cell0(_symId) with IntCell
class Cell0L(_symId: Int) extends Cell0(_symId) with RefCell

abstract class Cell1(_symId: Int, _acell0: Cell, _aport0: Int) extends Cell(_symId) {
  final var acell0: Cell = _acell0
  final var aport0: Int = _aport0
  final def arity: Int = 1
  final def auxCell(p: Int): Cell = acell0
  final def auxPort(p: Int): Int = aport0
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = { acell0 = c2; aport0 = p2 }
}
class Cell1V(_symId: Int, _acell0: Cell, _aport0: Int) extends Cell1(_symId, _acell0, _aport0) with VoidCell {
  def this(_symId: Int) = this(_symId, null, 0)
}
class Cell1I(_symId: Int, _acell0: Cell, _aport0: Int) extends Cell1(_symId, _acell0, _aport0) with IntCell {
  def this(_symId: Int) = this(_symId, null, 0)
}
class Cell1L(_symId: Int, _acell0: Cell, _aport0: Int) extends Cell1(_symId, _acell0, _aport0) with RefCell {
  def this(_symId: Int) = this(_symId, null, 0)
}

abstract class Cell2(_symId: Int, _acell0: Cell, _aport0: Int, _acell1: Cell, _aport1: Int) extends Cell(_symId) {
  final var acell0: Cell = _acell0
  final var aport0: Int = _aport0
  final var acell1: Cell = _acell1
  final var aport1: Int = _aport1
  final def arity: Int = 2
  final def auxCell(p: Int): Cell = if(p == 0) acell0 else acell1
  final def auxPort(p: Int): Int = if(p == 0) aport0 else aport1
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = if(p == 0) { acell0 = c2; aport0 = p2 } else { acell1 = c2; aport1 = p2 }
}
class Cell2V(_symId: Int, _acell0: Cell, _aport0: Int, _acell1: Cell, _aport1: Int) extends Cell2(_symId, _acell0, _aport0, _acell1, _aport1) with VoidCell {
  def this(_symId: Int) = this(_symId, null, 0, null, 0)
}
class Cell2I(_symId: Int, _acell0: Cell, _aport0: Int, _acell1: Cell, _aport1: Int) extends Cell2(_symId, _acell0, _aport0, _acell1, _aport1) with IntCell {
  def this(_symId: Int) = this(_symId, null, 0, null, 0)
}
class Cell2L(_symId: Int, _acell0: Cell, _aport0: Int, _acell1: Cell, _aport1: Int) extends Cell2(_symId, _acell0, _aport0, _acell1, _aport1) with RefCell {
  def this(_symId: Int) = this(_symId, null, 0, null, 0)
}

abstract class CellN(_symId: Int, val arity: Int) extends Cell(_symId) {
  private[this] final val auxCells = new Array[Cell](arity)
  private[this] final val auxPorts = new Array[Int](arity)
  final def auxCell(p: Int): Cell = auxCells(p)
  final def auxPort(p: Int): Int = auxPorts(p)
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = { auxCells(p) = c2; auxPorts(p) = p2 }
}
class CellNV(_symId: Int, _arity: Int) extends CellN(_symId, _arity) with VoidCell
class CellNI(_symId: Int, _arity: Int) extends CellN(_symId, _arity) with IntCell
class CellNL(_symId: Int, _arity: Int) extends CellN(_symId, _arity) with RefCell

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
  var rule: RulePlan = _
  def reduce(c1: Cell, c2: Cell, ptw: PerThreadWorker): Unit
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

  def reduce(_c1: Cell, _c2: Cell, ptw: PerThreadWorker): Unit = {
    val (c1, c2) = if(_c1.symId == s1id) (_c1, _c2) else (_c2, _c1)

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
      if(!b) return next.reduce(_c1, _c2, ptw)
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
      val c1 = cells(byte0(conn))
      val p1 = byte1(conn)
      val c2 = cells(byte2(conn))
      val p2 = byte3(conn)
      if(p1 >= 0) c1.setAux(p1, c2, p2)
      if(p2 >= 0) c2.setAux(p2, c1, p1)
      if((p1 & p2) < 0) ptw.createCut(c1, c2)
      i += 1
    }
  }

  def cellAllocationCount: Int = protoCells.length
}

final class Interpreter(globals: Symbols, rules: scala.collection.Map[RuleKey, RulePlan], compile: Boolean,
  debugBytecode: Boolean, val collectStats: Boolean) extends BaseInterpreter with SymbolIdLookup { self =>

  private[this] final val allSymbols = globals.symbols
  private[this] final val symIds = mutable.HashMap.from[Symbol, Int](allSymbols.zipWithIndex.map { case (s, i) => (s, i+1) })
  private[this] final val reverseSymIds = symIds.iterator.map { case (k, v) => (v, k) }.toMap
  private[this] final val symBits = Integer.numberOfTrailingZeros(Integer.highestOneBit(symIds.size))+1
  final val (ruleImpls, maxRuleCells, maxArity) = createRuleImpls()
  final val cutBuffer, irreducible = new CutBuffer(16)
  final val freeWires = mutable.HashSet.empty[Cell]

  def getAnalyzer: Analyzer[Cell] = new Analyzer[Cell] {
    def rootCells = (self.freeWires.iterator ++ (cutBuffer.iterator ++ principals.iterator).flatMap { case (c1, c2) => Seq(c1, c2) }).filter(_ != null).toSet
    val principals = mutable.HashMap.empty[Cell, Cell]
    (cutBuffer.iterator ++ irreducible.iterator).foreach { case (c1, c2) =>
      principals.put(c1, c2)
      principals.put(c2, c1)
    }
    def getSymbol(c: Cell): Symbol = c match {
      case c: WireCell => c.sym
      case c => reverseSymIds(c.symId)
    }
    def getPayload(c: Cell): Any = c.getGenericPayload
    def getConnected(c: Cell, port: Int): (Cell, Int) =
      if(port == -1) principals.get(c).map((_, -1)).getOrElse(null)
      else (c.auxCell(port), c.auxPort(port))
    def isFreeWire(c: Cell): Boolean = c.isInstanceOf[WireCell]
  }

  def setData(comp: Compiler): Unit = {
    cutBuffer.clear()
    irreducible.clear()
    freeWires.clear()
    val pairs = mutable.HashSet.empty[(Cell, Cell)]
    val scope = new Scope[Cell] {
      override val freeWires: mutable.HashSet[Cell] = self.freeWires
      def createCell(sym: Symbol, emb: Option[EmbeddedExpr]): Cell =
        if(sym.isCons) Cells.mk(getSymbolId(sym), sym.arity, Cells.cellKind(sym.arity, sym.payloadType)) else new WireCell(sym, 0)
      def connectCells(c1: Cell, p1: Int, c2: Cell, p2: Int): Unit = {
        if(p1 >= 0) c1.setAux(p1, c2, p2)
        if(p2 >= 0) c2.setAux(p2, c1, p1)
        if(p1 == -1 && p2 == -1 && !pairs.contains((c2, c1)) && pairs.add((c1, c2))) cutBuffer.addOne(c1, c2)
      }
    }
    comp.getData.foreach(scope.addData(_))
  }

  def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)
  def getSymbolId(name: String): Int = getSymbolId(globals(name))
  def createTempCells(): Array[Cell] = new Array[Cell](maxRuleCells)
  def createCutCache(): (Array[Cell], Array[Int]) = (new Array[Cell](maxArity*2), new Array[Int](maxArity*2))

  def createInterpretedRuleImpl(g: RulePlan, b: BranchPlan, next: Option[RuleImpl]): RuleImpl = {
    val pcs = b.cells.iterator.map(s => intOfShortByteByte(getSymbolId(s), s.arity, Cells.cellKind(s.arity, s.payloadType))).toArray
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
    if(compile)
      ParSupport.foreach(globals.symbols.filter(_.isCons))(codeGen.compileInterface(_, cl))
//    if(compile)
//      ParSupport.foreach(globals.symbols.filter(_.isCons))(codeGen.compileCons(_, rules, cl))
    ParSupport.foreach(rules.values) { g =>
      maxC.max(g.maxCells)
      maxA.max(g.arity1)
      maxA.max(g.arity2)
      val ri =
        if(compile) codeGen.compileRule(g, cl, this)
        else g.branches.foldRight(null: RuleImpl) { case (b, z) => createInterpretedRuleImpl(g, b, Option(z)) }
      ri.rule = g
      ris(mkRuleKey(getSymbolId(g.sym1), getSymbolId(g.sym2))) = ri
    }
    (ris, maxC.get, maxA.get)
  }

  @inline def mkRuleKey(c1: Cell, c2: Cell): Int = mkRuleKey(c1.symId, c2.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  // Used by the debugger
  def getRuleImpl(c1: Cell, c2: Cell): RuleImpl = ruleImpls(mkRuleKey(c1, c2))
  def reduce1(c1: Cell, c2: Cell): Unit = {
    val w = new PerThreadWorker(this)
    w.setNext(c1, c2)
    w.processNext()
    val (d1, d2) = w.getNext()
    if(d1 != null) cutBuffer.addOne(d1, d2)
  }

  def reduce(): Int = {
    val w = new PerThreadWorker(this)
    while(cutBuffer.nonEmpty) {
      val (wr, ri) = cutBuffer.pop()
      w.setNext(wr, ri)
      w.processAll()
    }
    if(collectStats)
      println(s"Total steps: ${w.steps}, allocated cells: ${w.cellAllocations}")
    w.steps
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

final class PerThreadWorker(final val inter: Interpreter) {
  final val tempCells = inter.createTempCells()
  final val (cutCacheCells, cutCachePorts) = inter.createCutCache()
  private[this] final var nextCut1, nextCut2: Cell = _
  private[this] final val collectStats = inter.collectStats
  var steps, cellAllocations = 0

  final def createCut(c1: Cell, c2: Cell): Unit = {
    if(nextCut1 == null) { nextCut1 = c1; nextCut2 = c2 }
    else inter.cutBuffer.addOne(c1, c2)
  }

  final def setNext(c1: Cell, c2: Cell): Unit = {
    this.nextCut1 = c1
    this.nextCut2 = c2
  }

  final def getNext(): (Cell, Cell) = (nextCut1, nextCut2)

  final def processNext(): Unit = {
    val c1 = nextCut1
    val c2 = nextCut2
    nextCut1 = null
    nextCut2 = null
    val ri = inter.ruleImpls(inter.mkRuleKey(c1, c2))
    if(ri != null) {
      ri.reduce(c1, c2, this)
      if(collectStats) {
        steps += 1
        cellAllocations += ri.cellAllocationCount
      }
    } else inter.irreducible.addOne(c1, c2)
  }

  @tailrec
  final def processAll(): Unit = {
    processNext()
    if(nextCut1 != null) processAll()
  }
}
