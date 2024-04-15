package de.szeiger.interact.sti

import de.szeiger.interact.codegen.ParSupport
import de.szeiger.interact._
import de.szeiger.interact.ast.{CompilationUnit, Label, PayloadType, Symbol, Symbols}
import de.szeiger.interact.BitOps._

import java.util.Arrays
import scala.collection.mutable

class Cell(val symId: Int, val arity: Int) {
  private[this] final val auxCells = new Array[Cell](arity)
  private[this] final val auxPorts = new Array[Int](arity)
  final def auxCell(p: Int): Cell = auxCells(p)
  final def auxPort(p: Int): Int = auxPorts(p)
  final def setAux(p: Int, c2: Cell, p2: Int): Unit = { auxCells(p) = c2; auxPorts(p) = p2 }
  final def getGenericPayload: Any = this match {
    case b: IntBox => b.getValue
    case b: RefBox => b.getValue
    case _ => ()
  }
  private[this] final def auxPortsIterator: Iterator[(Cell, Int)] = (0 until arity).iterator.map(i => (auxCell(i), auxPort(i)))
  override def toString = s"Cell($symId, $arity, [$getGenericPayload], ${auxPortsIterator.map { w => s"(${if(w._1 == null) "null" else s"${System.identityHashCode(w._1)}:${w._2}"})" }.mkString(", ") })@${System.identityHashCode(this)}"
  def cellSymbol: Symbol = null // managed via symId in Cells
}
object Cell {
  def apply(symId: Int, arity: Int, payloadType: PayloadType): Cell = payloadType match {
    case PayloadType.VOID => new Cell(symId, arity)
    case PayloadType.INT => new CellI(symId, arity)
    case _ => new CellR(symId, arity)
  }
}
final class CellI(_symId: Int, _arity: Int) extends Cell(_symId, _arity) with IntBox {
  private[this] final var payload: Int = 0
  def setValue(i: Int) = payload = i
  def getValue: Int = payload
}
final class CellR(_symId: Int, _arity: Int) extends Cell(_symId, _arity) with RefBox {
  private[this] final var payload: AnyRef = null
  def setValue(o: AnyRef) = payload = o
  def getValue: AnyRef = payload
}

final class WireCell(final val sym: Symbol) extends Cell(0, 1) {
  override def cellSymbol: Symbol = sym
  override def toString = s"WireCell($sym)@${System.identityHashCode(this)}"
}

final class RuleImpl(s1id: Int, protoCells: Array[Int], freeWiresPorts: Array[Int], connections: Array[Long],
    embeddedComps: Array[PayloadComputation], condComp: PayloadComputation, next: RuleImpl, sym1: Symbol, sym2: Symbol, val freeWires: Array[Symbol]) {

  override def toString = s"RuleImpl($sym1 <-> $sym2)"

  private[this] def payloadComp(pc: PayloadComputation, args: Array[Any]): Any = pc match {
    case pc: PayloadMethodApplication => pc.adaptedmh.invokeWithArguments(args: _*)
    case PayloadMethodApplicationWithReturn(m, _) =>
      val ret = payloadComp(m, args.init)
      args.last match {
        case b: IntBox => b.setValue(ret.asInstanceOf[Int])
        case b: RefBox => b.setValue(ret.asInstanceOf[AnyRef])
      }
    case _: PayloadAssignment =>
      args(1) match {
        case b: IntBox => b.setValue(args(0).asInstanceOf[Int])
        case b: RefBox => b.setValue(args(0).asInstanceOf[AnyRef])
      }
    case CreateLabelsComp(name, _) =>
      val label = new Label(name)
      args.foreach(_.asInstanceOf[RefBox].setValue(label))
      label
  }

  def reduce(_c1: Cell, _c2: Cell, ptw: Interpreter): Unit = try {
    val (c1, c2) = if(_c1.symId == s1id) (_c1, _c2) else (_c2, _c1)

    if(condComp != null) {
      val condArgs = condComp.embArgs
      var i = 0
      val args = new Array[Any](condArgs.length)
      while(i < condArgs.length) {
        args(i) = condArgs(i) match {
          case EmbArg.Active(0) => c1.getGenericPayload
          case EmbArg.Active(1) => c2.getGenericPayload
          case EmbArg.Const(v) => v
        }
        i += 1
      }
      val b = payloadComp(condComp, args).asInstanceOf[Boolean]
      if(!b) return next.reduce(_c1, _c2, ptw)
    }

    val cells = ptw.tempCells
    var i = 0
    while(i < protoCells.length) {
      val pc = protoCells(i)
      val sid = short0(pc)
      val ari = byte2(pc)
      val pt = byte3(pc)
      cells(i) = Cell(sid, ari, new PayloadType(pt))
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
            case EmbArg.Active(0) => c1.getGenericPayload
            case EmbArg.Active(1) => c2.getGenericPayload
            case EmbArg.Cell(n) => cells(n)
            case EmbArg.Const(v) => v
          }
          i += 1
        }
        payloadComp(embeddedComp, args)
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
      if((p1 & p2) < 0) ptw.addActive(cc1, cc2)
    }

    @inline def connectFreeToFree(ct1: Int, ct2: Int): Unit = {
      val cc1 = cccells(ct1)
      val p1 = ccports(ct1)
      val cc2 = cccells(ct2)
      val p2 = ccports(ct2)
      if(p1 >= 0) cc1.setAux(p1, cc2, p2)
      if(p2 >= 0) cc2.setAux(p2, cc1, p1)
      if((p1 & p2) < 0) ptw.addActive(cc1, cc2)
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
      if((p1 & p2) < 0) ptw.addActive(c1, c2)
      i += 1
    }

    if(ptw.metrics != null) ptw.metrics.recordStats(1, protoCells.length)
  } catch { case ex: Exception =>
    throw new RuntimeException(s"Error evaluating rule $this: $ex", ex)
  }
}

final class Interpreter(globals: Symbols, compilationUnit: CompilationUnit, config: Config) extends BaseInterpreter { self =>

  private[this] final val allSymbols = globals.symbols
  private[this] final val symIds = mutable.HashMap.from[Symbol, Int](allSymbols.zipWithIndex.map { case (s, i) => (s, i+1) })
  private[this] final val reverseSymIds = symIds.iterator.map { case (k, v) => (v, k) }.toMap
  private[this] final val symBits = Integer.numberOfTrailingZeros(Integer.highestOneBit(symIds.size))+1
  final val (ruleImpls, maxRuleCells, initialRuleImpls) = createRuleImpls()
  final val cutBuffer, irreducible = new CutBuffer(16)
  final val freeWires = mutable.HashSet.empty[Cell]
  var metrics: ExecutionMetrics = _
  final val tempCells = createTempCells()
  private[this] var nextCut1, nextCut2: Cell = _

  def getMetrics: ExecutionMetrics = metrics

  def getAnalyzer: Analyzer[Cell] = new Analyzer[Cell] {
    def irreduciblePairs: IterableOnce[(Cell, Cell)] = irreducible.iterator
    val principals = mutable.HashMap.empty[Cell, Cell]
    (cutBuffer.iterator ++ irreducible.iterator).foreach { case (c1, c2) =>
      principals.put(c1, c2)
      principals.put(c2, c1)
    }
    def rootCells = (self.freeWires.iterator ++ principals.keysIterator).toSet
    def getSymbol(c: Cell): Symbol = (c.cellSymbol, c) match {
      case (null, c: Cell) if c.symId != 0 => reverseSymIds(c.symId)
      case (null, _) => Symbol.NoSymbol
      case (s, _) => s
    }
    def getConnected(c: Cell, port: Int): (Cell, Int) =
      if(port == -1) principals.get(c).map((_, -1)).orNull
      else (c.auxCell(port), c.auxPort(port))
    def isFreeWire(c: Cell): Boolean = c.isInstanceOf[WireCell]
  }

  def initData(): Unit = {
    cutBuffer.clear()
    irreducible.clear()
    freeWires.clear()
    metrics = null
    initialRuleImpls.foreach { rule =>
      val free = rule.freeWires.map(new WireCell(_))
      freeWires.addAll(free)
      val lhs = Cell(0, freeWires.size, PayloadType.VOID)
      free.zipWithIndex.foreach { case (c, p) => lhs.setAux(p, c, 0) }
      rule.reduce(lhs, Cell(0, 0, PayloadType.VOID), this)
    }
    flushNext()
    metrics = if(config.collectStats) new ExecutionMetrics else null
  }

  def dispose(): Unit = ()

  def getSymbolId(sym: Symbol): Int = symIds.getOrElse(sym, 0)
  def createTempCells(): Array[Cell] = new Array[Cell](maxRuleCells)

  def createInterpretedRuleImpl(sym1Id: Int, r: GenericRuleWiring, b: BranchWiring, next: Option[RuleImpl]): RuleImpl = {
    val bp = new PackedBranchWiring(b, r)
    val pcs = b.cells.iterator.map(s => intOfShortByteByte(getSymbolId(s), s.arity, s.payloadType.value)).toArray
    new RuleImpl(sym1Id, pcs, bp.freeWiresPacked, bp.connectionsPackedLong,
      if(b.payloadComps.isEmpty) null else b.payloadComps.toArray, b.cond.orNull, next.orNull, r.sym1, r.sym2,
      r match {
        case r: InitialRuleWiring => r.free.toArray
        case _ => null
      })
  }

  def createRuleImpls(): (Array[RuleImpl], Int, Vector[RuleImpl]) = {
    val ris = new Array[RuleImpl](1 << (symBits << 1))
    val maxC = new ParSupport.AtomicCounter
    ParSupport.foreach(compilationUnit.statements.collect { case g: RuleWiring => g }, config.compilerParallelism) { g =>
      maxC.max(g.maxCells)
      val sym1Id = getSymbolId(g.sym1)
      val ri = g.branches.foldRight(null: RuleImpl) { case (b, z) => createInterpretedRuleImpl(sym1Id, g, b, Option(z)) }
      ris(mkRuleKey(sym1Id, getSymbolId(g.sym2))) = ri
    }
    val initial = Vector.newBuilder[RuleImpl]
    (compilationUnit.statements.collect { case i: InitialRuleWiring => i }).zipWithIndex.foreach { case (ip, i) =>
      maxC.max(ip.maxCells)
      initial += createInterpretedRuleImpl(0, ip, ip.branch, None)
    }
    (ris, maxC.get, initial.result())
  }

  @inline def mkRuleKey(c1: Cell, c2: Cell): Int = mkRuleKey(c1.symId, c2.symId)

  @inline def mkRuleKey(s1: Int, s2: Int): Int =
    if(s1 < s2) (s1 << symBits) | s2 else (s2 << symBits) | s1

  // Used by the debugger
  def getRuleImpl(c1: Cell, c2: Cell): RuleImpl = ruleImpls(mkRuleKey(c1, c2))
  def reduce1(c1: Cell, c2: Cell): Unit = {
    cutBuffer.remove(c1, c2)
    setNext(c1, c2)
    processNext()
    flushNext()
  }

  def reduce(): Unit =
    while(cutBuffer.nonEmpty) {
      val (c1, c2) = cutBuffer.pop()
      setNext(c1, c2)
      while(nextCut1 != null) processNext()
    }

  def addActive(c1: Cell, c2: Cell): Unit =
    if(nextCut1 == null) setNext(c1, c2) else cutBuffer.addOne(c1, c2)

  def setNext(c1: Cell, c2: Cell): Unit = {
    nextCut1 = c1
    nextCut2 = c2
  }

  def flushNext(): Unit =
    if(nextCut1 != null) {
      cutBuffer.addOne(nextCut1, nextCut2)
      setNext(null, null)
    }

  def processNext(): Unit = {
    val c1 = nextCut1
    val c2 = nextCut2
    setNext(null, null)
    val ri = ruleImpls(mkRuleKey(c1, c2))
    if(ri != null) ri.reduce(c1, c2, this)
    else irreducible.addOne(c1, c2)
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
  def iterator: Iterator[(Cell, Cell)] = pairs.iterator.take(len).grouped(2).map { case Seq(c1, c2) => (c1, c2) }
  // used by the debugger:
  def remove(c1: Cell, c2: Cell): Unit = {
    var i =0
    while(i < len) {
      val p1 = pairs(i)
      val p2 = pairs(i+1)
      if((c1 eq p1) && (c2 eq p2) || (c1 eq p2) && (c2 eq p1)) {
        System.arraycopy(pairs, i+2, pairs, i, len-i-2)
        len -= 2
        return
      }
      i += 2
    }
  }
}
