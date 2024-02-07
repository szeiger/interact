package de.szeiger.interact

import de.szeiger.interact.ast.{CompilationUnit, NamedNodesBuilder, Node, NodesBuilder, PayloadType, RuleKey, Statement, Symbol}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/** Translate RuleWiring/BranchWiring to RulePlan/BranchPlan for the code generator */
class PlanRules(global: Global) extends Phase {
  import global._
  import PlanRules._

  override def apply(u: CompilationUnit): CompilationUnit = {
    val rules = u.statements.collect { case r: RuleWiring => (r.key, r) }.toMap
    u.copy(u.statements.map {
      case n: RuleWiring => RulePlan(n.sym1, n.sym2, n.arity1, n.arity2, n.branches.map(b => createBranchPlan(Some(n), b, rules, 0, 0, -1, -1, Vector.empty)), None)
      case n: InitialRuleWiring => RulePlan(n.sym1, n.sym2, n.arity1, n.arity2, n.branches.map(b => createBranchPlan(Some(n), b, rules, 0, 0, -1, -1, Vector.empty)), Some(n.free))
      case s => s
    })
  }

  def createBranchPlan(rule: Option[GenericRuleWiring], branch: BranchWiring, rules: scala.collection.Map[RuleKey, RuleWiring],
    baseSingletonUse: Int, baseLabelCreate: Int, baseReuse1: Int, baseReuse2: Int, parentCells: Vector[Symbol]): BranchPlan = {
    val allCells = branch.cells ++ parentCells
    val (reuse1, reuse2, skipConns) = rule.map(findReuse(_, branch)).getOrElse((baseReuse1, baseReuse2, Set.empty[Connection]))
    val conns = (branch.intConns ++ branch.extConns).filterNot(skipConns.contains)
    val cellCreationOrder = optimizeCellCreationOrder(branch)
    val sortedConns = optimizeConnectionOrder(conns)
    val (createLabels, otherPayloadComps) = branch.payloadComps.partition(_.isInstanceOf[CreateLabelsComp])
    val createLabelComps = findLabels(allCells.length, createLabels.asInstanceOf[Vector[CreateLabelsComp]], reuse1, reuse2)
    //val (uniqueConts, uniqueContPoss) = uniqueContinuationsFor(rule, rules)
    val instructions = Vector.newBuilder[CreateInstruction]
    var statSingletonUse = baseSingletonUse
    val statLabelCreate = baseLabelCreate + createLabelComps.count(_.isInstanceOf[CreateLabelsComp])
    val cellPortsConnected = mutable.HashSet.empty[CellIdx]
    var cellPortsNotConnected = 0
    val cellsCreated = new Array[Boolean](branch.cells.length)
    instructions ++= (for(idx <- cellCreationOrder) yield {
      val idxO = idx + branch.cellOffset
      val instr = branch.cells(idx) match {
        case _ if idxO == reuse1 => Reuse1(idxO)
        case _ if idxO == reuse2 => Reuse2(idxO)
        case sym if isSingleton(sym) => statSingletonUse += 1; GetSingletonCell(idxO, sym)
        case sym => NewCell(idxO, sym, branch.auxConns(idx).iterator.zipWithIndex.map {
          case (CellIdx(ci, p2), p1) if !cellsCreated(idx) => cellPortsNotConnected += 1; CellIdx(-1, p2)
          case (CellIdx(ci, p2), p1) => cellPortsConnected += CellIdx(idx, p1); CellIdx(ci, p2)
          case (f: FreeIdx, _) => f
        }.toVector)
      }
      cellsCreated(idx) = true
      instr
    })
    val payloadTemp = computePayloadTemp(branch.cond.toVector ++ branch.payloadComps, branch.tempOffset)
    val payloadTempComps = payloadTemp.zipWithIndex.map { case ((pt, boxed), i) => AllocateTemp(EmbArg.Temp(i + branch.tempOffset, pt), boxed) }
    val payloadComps = payloadTempComps ++ createLabelComps ++ otherPayloadComps
    val loopOn1 = reuse1 != -1 && ((rule.get.sym1.isDef || reuse2 == -1) || !config.biasForCommonDispatch)
    val loopOn2 = reuse2 != -1 && ((rule.get.sym2.isDef || reuse1 == -1) || !config.biasForCommonDispatch)
    val branches = branch.branches.map(createBranchPlan(None, _, rules, statSingletonUse, statLabelCreate, reuse1, reuse2, allCells))
    val tempCount = payloadTemp.length + branches.map(_.totalTempCount).maxOption.getOrElse(0)
    branch.cond.foreach { case pc: PayloadMethodApplication => assert(pc.jMethod.getReturnType == classOf[Boolean]) }
    new BranchPlan(reuse1, reuse2, branch.cells, branch.cellOffset, branch.cond, sortedConns, payloadComps, tempCount,
      instructions.result(), cellPortsConnected, statSingletonUse, statLabelCreate, branches, loopOn1, loopOn2, branch.tempOffset)
  }

  // Find all temporary payload variables and whether or not they need to be boxed
  private def computePayloadTemp(pcs: Iterable[PayloadComputation], tempOffset: Int): Vector[(PayloadType, Boolean)] = {
    val payloadTemp = ArrayBuffer.empty[(PayloadType, Boolean)]
    def getPayloadTemp(i: Int) = if(i-tempOffset >= 0 && i-tempOffset < payloadTemp.length) payloadTemp(i-tempOffset) else null
    def setPayloadTemp(i: Int, pt: PayloadType, boxed: Boolean): Unit =
      if(i-tempOffset >= 0) {
        while(payloadTemp.length < i-tempOffset+1) payloadTemp += null
        payloadTemp(i-tempOffset) = ((pt, boxed))
      }
    def assign(ea: EmbArg, box: Boolean): Unit = ea match {
      case EmbArg.Temp(idx, pt) =>
        val old = getPayloadTemp(idx)
        setPayloadTemp(idx, pt, if(old == null) box else old._2 || box)
      case _ =>
    }
    def f(pc: PayloadComputation): Unit = pc match {
      case PayloadMethodApplication(embTp, args) => args.zip(embTp.args.map(_._2)).foreach { case (a, out) => assign(a, out) }
      case PayloadMethodApplicationWithReturn(m, ret) => f(m); assign(ret, false)
      case PayloadAssignment(src, target, _) => assign(src, false); assign(target, false)
      case CreateLabelsComp(_, args) => args.foreach(assign(_, false))
    }
    pcs.foreach(f)
    payloadTemp.foreach(t => assert(t != null))
    payloadTemp.toVector
  }

  private def findReuse(rule: GenericRuleWiring, branch: BranchWiring): (Int, Int, Set[Connection]) = {
    if(!config.reuseCells) return (-1, -1, Set.empty)

    // If cell(cellIdx) replaces rhs/lhs, how many connections stay the same?
    def countReuseConnections(cellIdxO: Int, rhs: Boolean): Int =
      reuseSkip(cellIdxO, rhs).length
    // Find connections to skip for reuse
    def reuseSkip(cellIdxO: Int, rhs: Boolean): IndexedSeq[Connection] =
      (0 until branch.cells(cellIdxO-branch.cellOffset).arity).flatMap { p =>
        val ci = new CellIdx(cellIdxO, p)
        branch.extConns.collect {
          case c @ Connection(FreeIdx(rhs2, fi2), ci2) if ci2 == ci && rhs2 == rhs && fi2 == p => c
          case c @ Connection(ci2, FreeIdx(rhs2, fi2)) if ci2 == ci && rhs2 == rhs && fi2 == p => c
        }
      }
    // Find cellIdxO/quality of best reuse candidate for rhs/lhs
    def bestReuse(candidates: Vector[Int], rhs: Boolean): Option[(Int, Int)] =
      candidates.map { i => (i, countReuseConnections(i, rhs)) }.maxByOption(_._2)
    // Find cellIdxO (i.e. with cellOffset) of cells with same symbol as rhs/lhs
    def reuseCandidates(rhs: Boolean): Vector[Int] =
      branch.cells.zipWithIndex.collect { case (sym, i) if sym == rule.symFor(rhs) => i + branch.cellOffset }

    // Find best reuse combination for both sides
    var cand1 = reuseCandidates(false)
    var cand2 = reuseCandidates(true)
    var best1 = bestReuse(cand1, false)
    var best2 = bestReuse(cand2, true)
    (best1, best2) match {
      case (Some((ci1, q1)), Some((ci2, q2))) if ci1 == ci2 =>
        if(q1 >= q2) { // redo best2
          cand2 = cand2.filter(_ != ci1)
          best2 = bestReuse(cand2, true)
        } else { // redo best1
          cand1 = cand1.filter(_ != ci2)
          best1 = bestReuse(cand1, false)
        }
      case _ =>
    }
    val skipConn1 = best1.iterator.flatMap { case (ci, _) => reuseSkip(ci, false) }
    val skipConn2 = best2.iterator.flatMap { case (ci, _) => reuseSkip(ci, true) }
    (best1.map(_._1).getOrElse(-1), best2.map(_._1).getOrElse(-1), (skipConn1 ++ skipConn2).toSet)
  }

  // Maximize # of connections that can be made in the constructor calls.
  // Returns a permutation of branch.cells, i.e. without applying the cellOffset.
  private def optimizeCellCreationOrder(branch: BranchWiring): Vector[Int] = {
    val co = branch.cellOffset
    val inc: Option[Int] => Option[Int] = { case Some(i) => Some(i+1); case None => Some(1) }
    lazy val cells = ArrayBuffer.tabulate(branch.cells.length)(new C(_))
    class C(val idx: Int) {
      val in, out = mutable.HashMap.empty[C, Int]
      var weight: Int = 0
      def link(c: C): Unit = {
        out.updateWith(c)(inc)
        c.in.updateWith(this)(inc)
        weight += 1
      }
      def unlink(): Unit = {
        out.keys.foreach(c => c.in.remove(this))
        in.keys.foreach(c => c.out.remove(this).foreach { w => c.weight -= w })
      }
    }
    branch.intConns.foreach { case Connection(CellIdx(i1, p1), CellIdx(i2, p2)) =>
      if(i1 >= co && i2 >= co) {
        if(p1 >= 0) cells(i1-co).link(cells(i2-co))
        if(p2 >= 0) cells(i2-co).link(cells(i1-co))
      }
    }
    val order = Vector.newBuilder[Int]
    def take() = {
      val c = cells.head
      cells.remove(0)
      order += c.idx
      c.unlink()
    }
    while(cells.nonEmpty) { //TODO use heap
      cells.sortInPlaceBy(c => c.weight)
      if(cells.head.weight == 0)
        while(cells.nonEmpty && cells.head.weight == 0) take()
      else take()
    }
    order.result()
  }

  private def optimizeConnectionOrder(conns: Set[Connection]): Vector[Connection] =
    conns.iterator.map {
      case Connection(i1, i2) if i1.port == -1 && i2.port != -1 => Connection(i2, i1)
      case Connection(i1: CellIdx, i2: FreeIdx) => Connection(i2, i1)
      case Connection(i1: FreeIdx, i2: FreeIdx) if (i1.rhs && !i2.rhs) || (i1.rhs == i2.rhs && i2.port < i1.port)  => Connection(i2, i1)
      case Connection(i1: CellIdx, i2: CellIdx) if i2.idx < i1.idx || (i2.idx == i1.idx && i2.port < i1.port) => Connection(i2, i1)
      case c => c
    }.toVector.sortBy {
      case Connection(CellIdx(idx, port),   _) => (0, idx, port)
      case Connection(FreeIdx(false, port), _) => (1, 0, port)
      case Connection(FreeIdx(true, port),  _) => (2, 0, port)
    }

  // Find unique continuation symbols for a rule plus a list of their eligible cell indices per branch
  private def uniqueContinuationsFor(rule: RuleWiring, rules: scala.collection.Map[RuleKey, RuleWiring]): (Set[Symbol], Vector[Vector[Int]]) = {
    if(config.inlineUniqueContinuations) {
      val funcSym =
        if(rule.derived) null
        else {
          val s = Set(rule.sym1, rule.sym2).filter(_.isDef)
          if(s.size == 1) s.head else null
        }
      if(funcSym != null) {
        val rhsSymsMap = rules.view.filterNot(_._2.derived).mapValues(_.branches.iterator.flatMap(_.cells).toSet)
        val rhsSymsHere = rhsSymsMap.iterator.filter { case (k, _) => k.sym1 == funcSym || k.sym2 == funcSym }.map(_._2).flatten.toSet
        val otherRhsSyms = rhsSymsMap.iterator.filter { case (k, _) => k.sym1 != funcSym && k.sym2 != funcSym }.map(_._2).flatten.toSet
        val unique = (rhsSymsHere -- otherRhsSyms).filter(s => s.isDef && s != funcSym && s.id != "dup" && s.id != "erase")
        val completions = rule.branches.map { branch =>
          (for {
            (s, i) <- branch.cells.zipWithIndex if unique.contains(s)
          } yield {
            branch.principalConns(i) match {
              case CellIdx(_, -1) => i //TODO not needed if rhs is fully reduced
              case FreeIdx(_, _) => i
              case _ => -1
          }}).filter(_ >= 0)
        }
        (unique, completions)
      } else (Set.empty, rule.branches.map(_ => Vector.empty))
    } else (Set.empty, rule.branches.map(_ => Vector.empty))
  }

  // Find suitable cell objects to reuse as labels
  private def findLabels(cellCount: Int, creators: Vector[CreateLabelsComp], reuse1: Int, reuse2: Int): Vector[PayloadComputationPlan] = {
    //TODO don't use cells from cell cache as labels
    var used = new Array[Boolean](cellCount)
    if(reuse1 != -1) used(reuse1) = true
    if(reuse2 != -1) used(reuse2) = true
    val assignments = Array.fill[Int](creators.length)(-1)
    // prefer cells the label gets assigned to
    for(i <- creators.indices) {
      val indices = creators(i).embArgs.collect { case EmbArg.Cell(idx) => idx }
      indices.find(!used(_)).foreach { idx =>
        used(idx) = true
        assignments(i) = idx
      }
    }
    // try to pick arbitrary free cells as a fallback
    for(i <- creators.indices if assignments(i) == -1) {
      val free = used.iterator.zipWithIndex.find(!_._1).map(_._2)
      free.foreach { idx =>
        used(idx) = true
        assignments(i) = idx
      }
    }
    creators.zip(assignments).map {
      case (cr, -1) => cr
      case (cr, idx) => ReuseLabelsComp(idx, cr.embArgs)
    }
  }
}

object PlanRules {
  def isSingleton(sym: Symbol) = sym.arity == 0 && sym.payloadType.isEmpty
}

final case class RulePlan(sym1: Symbol, sym2: Symbol, arity1: Int, arity2: Int, branches: Vector[BranchPlan],
  initialSyms: Option[Vector[Symbol]]) extends Statement {
  def initial = initialSyms.isDefined
  def show: String = s"sym1=$sym1, sym2=$sym2, arity1=$arity1, arity2=$arity2, initial=$initial"
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += branches
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
  def key: RuleKey = new RuleKey(sym1, sym2)
  def totalCellCount: Int = branches.map(_.totalCellCount).max
  def totalTempCount: Int = branches.map(_.totalTempCount).max
}

class BranchPlan(val reuse1: Int, val reuse2: Int,
  val cellSyms: Vector[Symbol],
  val cellOffset: Int,
  val cond: Option[PayloadComputationPlan],
  val sortedConns: Vector[Connection],
  val payloadComps: Vector[PayloadComputationPlan],
  val totalTempCount: Int,
  val cellCreateInstructions: Vector[CreateInstruction],
  val cellPortsConnected: mutable.HashSet[CellIdx],
  val statSingletonUse: Int,
  val statLabelCreate: Int,
  val branches: Vector[BranchPlan],
  val loopOn1: Boolean, val loopOn2: Boolean,
  val tempOffset: Int) extends Node {

  def isReuse(cellIdx: CellIdx): Boolean = cellIdx.idx == reuse1 || cellIdx.idx == reuse2
  def totalCellCount: Int = cellSyms.length + branches.map(_.totalCellCount).maxOption.getOrElse(0)

  def show: String = {
    val c = cellSyms.zipWithIndex.map { case (s, i) => s"${i + cellOffset}: $s/${s.arity}" }.mkString("cells = [", ", ", "]")
    s"reuse1=$reuse1, reuse2=$reuse2, loopOn1=$loopOn1, loopOn2=$loopOn2, cellO=$cellOffset, tempO=$tempOffset, $c"
  }
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) =
    n += (cond, "cond") += (cellCreateInstructions, "cc") += (sortedConns, "c") += (payloadComps, "pay") += (branches, "br")
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
}

sealed trait CreateInstruction extends Node
case class GetSingletonCell(cellIdx: Int, sym: Symbol) extends CreateInstruction {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$cellIdx, $sym")
}
case class Reuse1(cellIdx: Int) extends CreateInstruction {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$cellIdx")
}
case class Reuse2(cellIdx: Int) extends CreateInstruction {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$cellIdx")
}
case class NewCell(cellIdx: Int, sym: Symbol, args: Vector[Idx]) extends CreateInstruction {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$cellIdx, $sym, [${args.map(_.show).mkString(", ")}]")
}
