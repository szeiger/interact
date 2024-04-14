package de.szeiger.interact

import de.szeiger.interact.ast.{CompilationUnit, NamedNodesBuilder, Node, NodesBuilder, PayloadType, RuleKey, Statement, Symbol}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/** Translate RuleWiring/BranchWiring to RulePlan/BranchPlan for the code generator */
class PlanRules(val global: Global) extends Phase {
  import global._

  override def apply(u: CompilationUnit): CompilationUnit = {
    val rules = u.statements.collect { case r: RuleWiring => (r.key, r) }.toMap
    u.copy(u.statements.map {
      case n: RuleWiring => RulePlan(n.sym1, n.sym2, n.arity1, n.arity2, planBranchWirings(Some(n), n.branches, rules, 0, 0, Vector(-1, -1), Vector.empty), None)
      case n: InitialRuleWiring => RulePlan(n.sym1, n.sym2, n.arity1, n.arity2, planBranchWirings(Some(n), n.branches, rules, 0, 0, Vector(-1, -1), Vector.empty), Some(n.free))
      case s => s
    })
  }

  def planBranchWirings(rule: Option[GenericRuleWiring], branches: Vector[BranchWiring], rules: scala.collection.Map[RuleKey, RuleWiring],
      baseSingletonUse: Int, baseLabelCreate: Int, baseActive: Vector[Int], parentCells: Vector[Symbol]): RPStatement = {
    if(branches.length == 1)
      planBranchWiring(rule, branches.head, rules, baseSingletonUse, baseLabelCreate, baseActive, parentCells)
    else {
      val brs = branches.map { bw =>
        bw.cond.foreach {
          case pc: PayloadMethodApplication => assert(pc.jMethod.getReturnType == classOf[Boolean])
          case _: CheckPrincipal =>
        }
        (bw.cond.getOrElse(null), planBranchWiring(rule, bw, rules, baseSingletonUse, baseLabelCreate, baseActive, parentCells))
      }
      optimizeCondition(RPCond(brs.init, Some(brs.last._2)))
    }
  }

  // find sequence of multiple CheckPrincipal conditions on the same wire
  private def findCPSeq(ifThen: Vector[(PayloadComputationPlan, _)]): Option[(Int, Int)] = {
    var start = -1
    var wire: Idx = null
    for(i <- ifThen.indices) {
      if(start == -1) {
        ifThen(i) match {
          case (CheckPrincipal(w, _, _), _) => wire = w; start = i
          case _ => ()
        }
      } else {
        ifThen(i) match {
          case (CheckPrincipal(w, _, _), _) if w == wire => ()
          case _ => return Some((start, i))
        }
      }
    }
    if(start == -1) None else Some((start, ifThen.length))
  }

  def optimizeCondition(cond: RPCond): RPStatement = {
    findCPSeq(cond.ifThen) match {
      case Some((start, end)) =>
        val wire = cond.ifThen(start)._1.asInstanceOf[CheckPrincipal].wire
        val matches = cond.ifThen.slice(start, end).map { case (CheckPrincipal(_, s , _), t) => (s, t) }
        val pre = cond.ifThen.slice(0, start)
        val post = cond.ifThen.drop(end)
        val m = RPMatchPrincipal(wire.asInstanceOf[FreeIdx], matches, if(post.isEmpty) cond.els else Some(optimizeCondition(RPCond(post, cond.els))))
        if(pre.isEmpty) m else RPCond(pre, Some(m))
      case None => cond
    }
  }

  def planBranchWiring(rule: Option[GenericRuleWiring], branch: BranchWiring, rules: scala.collection.Map[RuleKey, RuleWiring],
    baseSingletonUse: Int, baseLabelCreate: Int, baseActive: Vector[Int], parentCells: Vector[Symbol]): RPStatement = {
    lazy val ruleWiring: Option[RuleWiring] = rule.collect { case r: RuleWiring => r }
    lazy val initialRuleWiring: Option[InitialRuleWiring] = rule.collect { case r: InitialRuleWiring => r }
    val allCells = parentCells ++ branch.cells
    val (active, skipConns) = rule.map(findReuse(_, branch)).getOrElse((baseActive, Set.empty[Connection]))
    //println(s"${rule.map(r => r.sym1 + ", " + r.sym2)} $active")
    val conns = (branch.intConns ++ branch.extConns).filterNot(skipConns.contains)
    val cellCreationOrder = optimizeCellCreationOrder(branch)
    val instr1, instr2 = Vector.newBuilder[Instruction]
    var statSingletonUse = baseSingletonUse
    val cellPortsConnected = mutable.HashSet.empty[CellIdx]
    var cellPortsNotConnected = 0
    val cellsCreated = new Array[Boolean](branch.cells.length)
    branch.cond.foreach {
      case CheckPrincipal(wire, sym, activeIdx) => instr1 += ActivateCell(wire, sym, activeIdx)
      case _ =>
    }
    for(idx <- cellCreationOrder) {
      val idxO = idx + branch.cellOffset
      val activeForIdxO = active.indexOf(idx)
      branch.cells(idx) match {
        case sym if activeForIdxO >= 0 && (!config.unboxedPrimitives || !config.backend.canUnbox(sym)) => instr1 += ReuseActiveCell(idxO, activeForIdxO, sym)
        case sym if sym.isSingleton && (!config.unboxedPrimitives || !config.backend.canUnbox(sym)) => statSingletonUse += 1; instr2 += GetSingletonCell(idxO, sym)
        case sym => instr2 += NewCell(idxO, sym, branch.auxConns(idx).iterator.zipWithIndex.map {
          case (CellIdx(ci, p2), p1) if !cellsCreated(ci) && active.indexOf(ci) < 0 => cellPortsNotConnected += 1; CellIdx(-1, p2)
          //case (CellIdx(ci, p2), p1) if !cellsCreated(idx) && ci != reuse1 && ci != reuse2 => cellPortsNotConnected += 1; CellIdx(-1, p2)
          case (CellIdx(ci, p2), p1) => cellPortsConnected += CellIdx(idx, p1); CellIdx(ci, p2)
          case (f: FreeIdx, _) => f
        }.toVector)
      }
      cellsCreated(idx) = true
    }
    instr1 ++= instr2.result()
    val sortedConns = optimizeConnectionOrder(conns, cellPortsConnected)
    val filteredPayloadComps = branch.payloadComps.filter { // skip identity assignments to reused cells
      case pc @ PayloadAssignment(EmbArg.Active(a), EmbArg.Cell(i), _) => active(a) != i
      case _ => true
    }
    val (createLabels, otherPayloadComps) = filteredPayloadComps.partition(_.isInstanceOf[CreateLabelsComp])
    val createLabelComps =
      if(config.backend.canReuseLabels) findLabels(allCells.length, createLabels.asInstanceOf[Vector[CreateLabelsComp]], active)
      else createLabels
    val statLabelCreate = baseLabelCreate + createLabelComps.count(_.isInstanceOf[CreateLabelsComp])
    val allPayloadComps = branch.cond.toVector ++ filteredPayloadComps
    val needsCachedPayloads = allPayloadComps.iterator.flatMap(_.embArgs).collect { case EmbArg.Active(i) => i }.toSet
    val payloadTemp = computePayloadTemp(allPayloadComps, branch.tempOffset)
    val payloadTempComps = payloadTemp.zipWithIndex.map { case ((pt, boxed), i) => AllocateTemp(EmbArg.Temp(i + branch.tempOffset, pt), boxed) }
    val payloadComps = payloadTempComps ++ createLabelComps ++ otherPayloadComps
    def canBeActive(idx: Idx) = idx match {
      case CellIdx(i, p) => p < 0
      case _ => true
    }
    def isLoop(reuse: Int, otherReuse: Int, sym: => Symbol) =
      reuse != -1 && rule.isDefined && sym == branch.cells(reuse) && config.loop && canBeActive(branch.principalConns(reuse)) &&
        (sym.isDef || otherReuse == -1 || !config.biasForCommonDispatch)
    val loopOn0 = isLoop(active(0), active(1), rule.get.sym1)
    val loopOn1 = isLoop(active(1), active(0), rule.get.sym2)
    val utail = ruleWiring match {
      case Some(r) =>
        val cand = sortedConns.iterator.collect { case Connection(CellIdx(i1, -1), CellIdx(i2, -1)) => (allCells(i1), allCells(i2)) }.toVector
        val pref = cand.find { case (s1, s2) => (s1 == r.sym1 && s2 == r.sym2) || (s1 == r.sym2 && s2 == r.sym1) }.map { _ => (r.sym1, r.sym2) }
        pref.orElse(cand.headOption)
      case _ => None
    }
    val (tailSyms0, tailSyms1, useTailCont) = if(branch.branches.isEmpty) { //TODO support all branches
      val pairs = sortedConns.iterator.flatMap {
        case Connection(CellIdx(i1, -1), CellIdx(i2, -1)) => Vector((allCells(i1), allCells(i2), true))
        case Connection(CellIdx(i1, -1), FreeIdx(_, _)) => Vector((allCells(i1), Symbol.NoSymbol, true))
        case _ => Vector.empty
      }.toVector
      (pairs.map(_._1).toSet, pairs.map(_._2).toSet, initialRuleWiring.isEmpty && pairs.exists(_._3))
    } else (Set.empty[Symbol], Set.empty[Symbol], false)
    val nested =
      if(branch.branches.isEmpty) None
      else Some(planBranchWirings(None, branch.branches, rules, statSingletonUse, statLabelCreate, active, allCells))
    new BranchPlan(active, branch.cells, branch.cellOffset, sortedConns, payloadComps,
      instr1.result(), cellPortsConnected, branch.statSteps, statSingletonUse, statLabelCreate, nested,
      utail, loopOn0, loopOn1, tailSyms0, tailSyms1, useTailCont, branch.tempOffset, needsCachedPayloads)
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
      case _ =>
    }
    pcs.foreach(f)
    payloadTemp.foreach(t => assert(t != null))
    payloadTemp.toVector
  }

  private def findReuse(rule: GenericRuleWiring, branch: BranchWiring): (Vector[Int], Set[Connection]) = {
    if(!config.reuseCells || rule.isInstanceOf[InitialRuleWiring])
      return (Vector(-1, -1) ++ branch.cond.collect { case pc: CheckPrincipal => -1 }, Set.empty)

    val activeSyms = Vector(rule.sym1, rule.sym2) ++ branch.cond.collect { case pc: CheckPrincipal => pc.sym }

    // If cell(cellIdx) replaces rhs/lhs, how many connections stay the same?
    def countReuseConnections(cellIdxO: Int, ac: Int): Int =
      reuseSkip(cellIdxO, ac).length
    // Find connections to skip for reuse
    def reuseSkip(cellIdxO: Int, ac: Int): Vector[Connection] =
      (0 until branch.cells(cellIdxO-branch.cellOffset).arity).iterator.flatMap { p =>
        val ci = new CellIdx(cellIdxO, p)
        branch.extConns.collect {
          case c @ Connection(FreeIdx(ac2, fi2), ci2) if ci2 == ci && ac2 == ac && fi2 == p => c
          case c @ Connection(ci2, FreeIdx(ac2, fi2)) if ci2 == ci && ac2 == ac && fi2 == p => c
        }
      }.toVector
    def storageClass(sym: Symbol) =
      if(config.unboxedPrimitives && config.backend.canUnbox(sym)) sym
      else config.backend.storageClass(sym)
    def canReuse(sym: Symbol, ac: Int) =
      !sym.isSingleton && storageClass(sym) == storageClass(activeSyms(ac))
    // Find cellIdxO (i.e. with cellOffset) and quality of cells with same symbol as an active cell
    def reuseCandidates(ac: Int): ArrayBuffer[(Int, Int)] =
      branch.cells.iterator.zipWithIndex.collect { case (sym, i) if canReuse(sym, ac) =>
        val iO = i + branch.cellOffset
        (iO, countReuseConnections(iO, ac) + (if(sym == activeSyms(ac)) 1 else 0))
      }.to(ArrayBuffer)

    // Find best reuse combination for all active cells
    val cand = activeSyms.indices.iterator.map(i => i -> reuseCandidates(i).sortBy(-_._2)).filter(_._2.nonEmpty).to(mutable.HashMap)
    val reuse = Array.fill(activeSyms.length)(-1)
    while(cand.nonEmpty) {
      val (bestA, (ciO, _)) = cand.iterator.map { case (a, rs) => (a, rs.head) }.toVector.maxBy(-_._2._2)
      reuse(bestA) = ciO
      cand.remove(bestA)
      cand.filterInPlace { (_, rs) =>
        rs.filterInPlace(_._1 != ciO)
        rs.nonEmpty
      }
    }

    val skipConn = reuse.iterator.zipWithIndex.flatMap {
      case (ciO, ac) if ciO != -1 => reuseSkip(ciO, ac)
      case _ => Vector.empty
    }
    (reuse.toVector, skipConn.toSet)
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
    val res = order.result()
    if(config.unboxedPrimitives) { // "create" unboxed values last so they get connected later when we have the values
      val (unboxed, normal) = res.partition(i => config.backend.canUnbox(branch.cells(i)))
      normal ++ unboxed
    } else res
  }

  private def optimizeConnectionOrder(conns: Set[Connection], cellPortsConnected: mutable.HashSet[CellIdx]): Vector[Connection] =
    conns.iterator.filter {
      case Connection(i1: CellIdx, i2: CellIdx) =>
        // pre-filter when both directions are unnecessary
        if((i1.port == -1) != (i2.port == -1) && (cellPortsConnected.contains(i1) || cellPortsConnected.contains(i2))) false
        else true
      case _ => true
    }.map {
      case Connection(i1, i2) if i1.port != -1 && i2.port == -1 => Connection(i2, i1)
      case Connection(i1: FreeIdx, i2: CellIdx) => Connection(i2, i1)
      case Connection(i1: FreeIdx, i2: FreeIdx) if (i2.active >= i1.active) || (i2.active == i1.active && i1.port < i2.port)  => Connection(i2, i1)
      case Connection(i1: CellIdx, i2: CellIdx) if i1.idx < i2.idx || (i1.idx == i2.idx && i1.port < i2.port) => Connection(i2, i1)
      case c => c
    }.toVector.sortBy {
      case Connection(CellIdx(idx, port), _) => (0, idx, port)
      case Connection(FreeIdx(a, port), _) => (a+1, 0, port)
    }

  // Find suitable cell objects to reuse as labels
  private def findLabels(cellCount: Int, creators: Vector[CreateLabelsComp], active: Vector[Int]): Vector[PayloadComputationPlan] = {
    //TODO don't use cells from cell cache as labels
    var used = new Array[Boolean](cellCount)
    active.foreach { a => if(a != -1) used(a) = true }
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

final case class RulePlan(sym1: Symbol, sym2: Symbol, arity1: Int, arity2: Int, statement: RPStatement,
  initialSyms: Option[Vector[Symbol]]) extends Statement {
  def initial = initialSyms.isDefined
  def show: String = s"$key, arity1=$arity1, arity2=$arity2, initial=$initial"
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += statement
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
  def key: RuleKey = new RuleKey(sym1, sym2)

  lazy val (totalCellCount, totalTempCount, totalActiveCount) = {
    var c, t, a = 0
    def f(n: Node): Unit = {
      n match {
        case n: BranchPlan => a = a.max(n.active.length-1)
        case n: PayloadComputationPlan => n.embArgs.foreach {
          case n: EmbArg.Temp => t = t.max(n.idx)
          case _ =>
        }
        case n: CellCreateInstruction => c = c.max(n.cellIdx)
        case _ =>
      }
      n.nodeChildren.foreach(f)
    }
    f(this)
    (c+1, t+1, (a+1).max(2))
  }
}

sealed trait RPStatement extends Node {
  def needsCachedPayloads: Set[Int]
  def branchPlans: Iterator[BranchPlan]
}

case class RPCond(ifThen: Vector[(PayloadComputationPlan, RPStatement)], els: Option[RPStatement]) extends RPStatement {
  def branchPlans: Iterator[BranchPlan] = ifThen.iterator.flatMap { case (_, t) => t.branchPlans } ++ els.iterator.flatMap(_.branchPlans)
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = {
    ifThen.zipWithIndex.foreach { case ((i, t), idx) => n += (i, s"if$idx"); n += (t, s"then$idx") }
    n += (els, "else")
  }
  lazy val needsCachedPayloads: Set[Int] = (ifThen.map(_._2) :++ els).flatMap(_.needsCachedPayloads).toSet
}

case class RPMatchPrincipal(wire: FreeIdx, ifThen: Vector[(Symbol, RPStatement)], els: Option[RPStatement]) extends RPStatement {
  def branchPlans: Iterator[BranchPlan] = ifThen.iterator.flatMap { case (_, t) => t.branchPlans } ++ els.iterator.flatMap(_.branchPlans)
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$wire, ${ifThen.map(_._1).mkString("[", ", ", "]")}")
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) = n += ifThen.map(_._2) += (els, "else")
  lazy val needsCachedPayloads: Set[Int] = ifThen.map(_._2).flatMap(_.needsCachedPayloads).toSet
}

class BranchPlan(val active: Vector[Int],
  val cellSyms: Vector[Symbol],
  val cellOffset: Int,
  val sortedConns: Vector[Connection],
  val payloadComps: Vector[PayloadComputationPlan],
  val instructions: Vector[Instruction],
  val cellPortsConnected: mutable.HashSet[CellIdx],
  val statSteps: Int,
  val statSingletonUse: Int,
  val statLabelCreate: Int,
  val nested: Option[RPStatement],
  val unconditionalTail: Option[(Symbol, Symbol)],
  val loopOn0: Boolean, val loopOn1: Boolean,
  val tailSyms0: Set[Symbol], val tailSyms1: Set[Symbol],
  val useTailCont: Boolean,
  val tempOffset: Int,
  val needsCachedPayloads: Set[Int]) extends RPStatement {

  def branchPlans: Iterator[BranchPlan] = Iterator.single(this)
  def isReuse(cellIdx: CellIdx): Boolean = active.contains(cellIdx.idx)
  def singleDispatchSym0: Symbol = if(tailSyms0.size == 1) tailSyms0.head else Symbol.NoSymbol
  def singleDispatchSym1: Symbol = if(tailSyms1.size == 1) tailSyms1.head else Symbol.NoSymbol
  def useLoopCont: Boolean = loopOn0 || loopOn1

  def show: String = {
    val c = cellSyms.zipWithIndex.map { case (s, i) => s"${i + cellOffset}: $s/${s.arity}" }.mkString("cells = [", ", ", "]")
    val n = needsCachedPayloads.mkString("{", ", ", "}")
    s"a=${active.mkString("[", ", ", "]")}, loop0=$loopOn0, loop1=$loopOn1, utail=$unconditionalTail, useTailCont=$useTailCont, sd0=$singleDispatchSym0, sd1=$singleDispatchSym1, cellO=$cellOffset, tempO=$tempOffset, needsCP=$n, steps=$statSteps\n$c"
  }
  override protected[this] def buildNodeChildren[N <: NodesBuilder](n: N) =
    n += (instructions, "cc") += (payloadComps, "p") += (sortedConns, "c") += nested
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(show)
}

sealed trait Instruction extends Node

sealed trait CellCreateInstruction extends Instruction {
  def cellIdx: Int
}
case class GetSingletonCell(cellIdx: Int, sym: Symbol) extends CellCreateInstruction {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$cellIdx, $sym")
}
case class ReuseActiveCell(cellIdx: Int, activeIdx: Int, sym: Symbol) extends CellCreateInstruction {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$cellIdx, active($activeIdx), $sym")
}
case class NewCell(cellIdx: Int, sym: Symbol, args: Vector[Idx]) extends CellCreateInstruction {
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$cellIdx, $sym, [${args.map(_.show).mkString(", ")}]")
}

final case class ActivateCell(wire: Idx, sym: Symbol, activeIdx: Int) extends Instruction {
  val embArgs: Vector[EmbArg] = Vector.empty
  override protected[this] def namedNodes: NamedNodesBuilder = new NamedNodesBuilder(s"$wire, $sym at a($activeIdx)")
}
