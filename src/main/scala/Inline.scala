package de.szeiger.interact

import de.szeiger.interact.ast.{CompilationUnit, RuleKey, ShowableNode, Statement, Symbol, Transform}

import scala.collection.mutable

/**
 * Inline active pairs on the RHS of rules.
 */
class Inline(global: Global) extends Phase {
  import global._

  def apply(n: CompilationUnit): CompilationUnit = {
    val allInlinableRules = n.statements.iterator.collect {
      case r: RuleWiring if config.compile || (r.branches.length == 1 && r.sym1.payloadType.isEmpty && r.sym2.payloadType.isEmpty) => (r.key, r)
    }.toMap
    val (fullyInlinableRules, chainableRules) = allInlinableRules.partition(_._2.branches.length == 1)
    checkCircular(fullyInlinableRules)
    val n2 = if(config.inlineFull) transformer(fullyInlinableRules, false)(n) else n
    val n3 = if(config.compile && config.inlineBranching) transformer(chainableRules, true)(n2) else n2
    if(config.inlineUniqueContinuations && config.compile) {
      val rules = n3.statements.iterator.collect { case r: RuleWiring => (r.key, r) }.toMap
      activateTransform(rules)(n3)
    } else n3
  }

  private[this] def activateTransform(rules: Map[RuleKey, RuleWiring]): Transform = new Transform {
    override def apply(r: RuleWiring) = Vector({
      val uniqueContSyms = uniqueContinuationsFor(r, rules)
      if(uniqueContSyms.nonEmpty) {
        //println(s"**** Unique continuations for ${r.key}: $uniqueContSyms")
        r.copy(branches = r.branches.flatMap(createConinuationMatches(r, _, uniqueContSyms, rules)))
      } else r
    })
  }

  private[this] def createConinuationMatches(rule: RuleWiring, branch: BranchWiring, uniqueContSyms: Set[Symbol], rules: Map[RuleKey, RuleWiring]): Vector[BranchWiring] = {
    assert(branch.cellOffset == 0)
    val candidates = branch.cells.iterator.zipWithIndex.flatMap {
      case (s, i) if uniqueContSyms.contains(s) =>
        branch.principalConns(i) match {
          case f: FreeIdx => Iterator.single(s, i, f)
          case _ => Iterator.empty
        }
      case _ => Iterator.empty
    }.toVector
    if(candidates.nonEmpty) {
      //println("Candidates in branch: " + candidates)
      val (usym, idx, wire) = candidates.head //TODO support multiple?
      val partners = rules.iterator.filterNot(_._2.derived).collect {
        case (k, r) if k.sym1 == usym => (k.sym2, r)
        case (k, r) if k.sym2 == usym => (k.sym1, r)
      }.toVector
      if(branch.cond.isEmpty) {
        //ShowableNode.print(branch, name = "Original branch")
        partners.map { case (psym, prule) =>
          //println(s"Activating branch of ${rule.key} with ($idx, $usym, $psym, $wire):")
          val b = makeActive(branch, psym, wire)
          val (c1, c2) = if(prule.key.sym1 == usym) (idx, b.cells.length-1) else (b.cells.length-1, idx)
          assert(b.branches.isEmpty)
          //ShowableNode.print(b, name = s"Inlining into at $c1, $c2")
          //ShowableNode.print(prule, name = "Inlining")
          val b2 = inline(b, c1, c2, prule)._1
          //ShowableNode.print(b2, name = "Activated")
          b2
        } :+ branch
      } else {
        Vector(branch) //--
      }
    } else Vector(branch)
  }

  def makeActive(branch: BranchWiring, psym: Symbol, pWire: FreeIdx): BranchWiring = {
    val topCellLen = branch.cells.length
    val tr = new Transform {
      override def apply(n: BranchWiring) =
        super.apply(n.copy(cellOffset = n.cellOffset + 1))
      override def apply(n: EmbArg): EmbArg = n match {
        case EmbArg.Cell(i) if i >= topCellLen => EmbArg.Cell(i + 1)
        case n => n
      }
      override def apply(n: Connection): Set[Connection] = {
        def mapIdx(c: Idx) = c match {
          case c if c == pWire => CellIdx(topCellLen, -1)
          case CellIdx(i, p) if i >= topCellLen => CellIdx(i + 1, p)
          case c => c
        }
        val c1a = mapIdx(n.c1)
        val c2a = mapIdx(n.c2)
        if((c1a eq n.c1) && (c2a eq n.c2)) Set(n)
        else Set(Connection(c1a, c2a))
      }
    }
    val b1 = tr(branch)
    val activeIdx = 2
    val newPayloadComps =
      if(psym.payloadType.isDefined) Vector(PayloadAssignment(EmbArg.Active(activeIdx), EmbArg.Cell(topCellLen), psym.payloadType))
      else Vector.empty
    val newConns = (0 until psym.arity).map(i => Connection(CellIdx(topCellLen, i), FreeIdx(activeIdx, i)))
    val b2 = b1.copy(cellOffset = b1.cellOffset-1, cond = Some(CheckPrincipal(pWire, psym, activeIdx)),
      cells = b1.cells :+ psym, conns = b1.conns ++ newConns, statSteps = b1.statSteps + 1,
      payloadComps = newPayloadComps ++ b1.payloadComps)
    b2
  }

  private[this] def transformer(inlinableRules: Map[RuleKey, RuleWiring], chained: Boolean): Transform = new Transform {
    val processed = mutable.Map.empty[RuleKey, RuleWiring]
    override def apply(n: Statement): Vector[Statement] = n match {
      case n: RuleWiring => apply(n)
      case n => Vector(n)
    }
    override def apply(n: RuleWiring): Vector[Statement] = Vector(processRuleWiring(n, Set.empty))
    def processRuleWiring(n: RuleWiring, via: Set[RuleKey]): RuleWiring = processed.get(n.key) match {
      case Some(r) => r
      case None if via.contains(n.key) => n
      case None =>
        val br2 = n.branches.zipWithIndex.map { case (b, i) => inlineInto(b, n.key, i, via) }
        val n2 = n.copy(branches = br2)
        if(!config.inlineDuplicate) processed.put(n.key, n2)
        n2
    }
    def inlineInto(n: BranchWiring, key: RuleKey, branchIdx: Int, via: Set[RuleKey]): BranchWiring = {
      assert(n.cellOffset == 0 && n.branches.isEmpty, s"in $key #$branchIdx")
      val pairs = findInlinable(n, inlinableRules).collect { case (c1, c2, r) if key != r.key => (c1, c2, processRuleWiring(r, via + key)) }
      if(pairs.isEmpty) n
      else {
        //if(chained) println(s"***** inlining into ${key} #$branchIdx: ${pairs.map(_._3.key)}, via: $via")
        def inlineAll(n: BranchWiring, ps: List[(Int, Int, RuleWiring)]): BranchWiring = ps match {
          case (c1, c2, r) :: ps =>
            val (n2, mapping) = inline(n, c1, c2, r)
            inlineAll(n2, ps.map { case (c1, c2, r) => (mapping(c1), mapping(c2), r) })
          case Nil => n
        }
        if(chained) inlineAll(n, pairs.toList.take(1))
        else inlineAll(n, pairs.toList)
      }
    }
  }

  private[this] def checkCircular(inlinableRules: Map[RuleKey, RuleWiring]): Unit = {
    val directInlinable = (for {
      (k, r) <- inlinableRules.iterator
    } yield k -> findInlinable(r.branches.head, inlinableRules).iterator.map(_._3).toVector).toMap

    def check(r: RuleWiring, used: Set[RuleKey], usedList: List[RuleKey]): Unit = {
      if(used.contains(r.key)) error(s"Circular expansion ${usedList.reverse.map(k => s"($k)").mkString(" => ")}", r.branches.head)
      else {
        val direct = directInlinable.getOrElse(r.key, Vector.empty)
        val subUsed = used + r.key
        val subUsedList = r.key :: usedList
        direct.sortBy(_.pos).foreach { r2 => check(r2, subUsed, subUsedList) }
      }
    }
    inlinableRules.values.toVector.sortBy(_.pos).foreach(check(_, Set.empty, Nil))
    checkThrow()
  }

  private[this] def findInlinable(n: BranchWiring, rules: Map[RuleKey, RuleWiring]): Set[(Int, Int, RuleWiring)] =
    n.intConns.iterator.collect { case Connection(CellIdx(c1, -1), CellIdx(c2, -1)) =>
      (c1, c2, rules.get(new RuleKey(n.cells(c1), n.cells(c2))))
    }.collect { case (c1, c2, Some(r)) =>
      if(n.cells(c1) == r.sym1)  (c1, c2, r) else (c2, c1, r)
    }.toSet

  private[this] def inline(outer: BranchWiring, c1: Int, c2: Int, inner: RuleWiring): (BranchWiring, Map[Int, Int]) = {
    //println(s"inline($c1, $c2)")
    assert(outer.cellOffset == 0 && outer.branches.isEmpty)
    //ShowableNode.print(b, name = s"inlining ${r.key} into")
    val outerCellsIndexed = outer.cells.iterator.zipWithIndex.filter { case (_, i) => i != c1 && i != c2 }.toVector
    val outerCells = outerCellsIndexed.map(_._1)
    val outerCellsMapping = outerCellsIndexed.iterator.map(_._2).zipWithIndex.map { case (iold, inew) => iold -> inew }.toMap
    val innerCellOffset = outerCells.length
    val innerMapping = mutable.HashMap.empty[Idx, Idx]
    val outerTempCount = tempCount(outer.payloadComps ++ outer.cond)
    val c1Temp = if(outer.cells(c1).payloadType.isDefined) EmbArg.Temp(outerTempCount, outer.cells(c1).payloadType) else null
    val c2Temp = if(outer.cells(c2).payloadType.isDefined) EmbArg.Temp(if(c1Temp != null) outerTempCount+1 else outerTempCount, outer.cells(c2).payloadType) else null
    val innerTempOffset = outerTempCount + (if(c1Temp != null) 1 else 0) + (if(c2Temp != null) 1 else 0)

    val relabelOuter: Transform = new Transform {
      override def apply(n: EmbArg): EmbArg = n match {
        case EmbArg.Cell(i) if i == c1 => c1Temp
        case EmbArg.Cell(i) if i == c2 => c2Temp
        case EmbArg.Cell(i) => EmbArg.Cell(outerCellsMapping(i))
        case n => n
      }
      override def apply(n: Connection): Set[Connection] = {
        def remapO(idx: Idx) = idx match {
          case CellIdx(i, p) => CellIdx(outerCellsMapping(i), p)
          case _ => idx
        }
        def remapI(idx: Idx) = idx match {
          case CellIdx(i, p) if i == c1 => FreeIdx(0, p)
          case CellIdx(i, p) if i == c2 => FreeIdx(1, p)
          case _ => idx
        }
        val nc1i = remapI(n.c1)
        val nc2i = remapI(n.c2)
        if(nc1i ne n.c1) innerMapping.update(nc1i, remapO(nc2i))
        if(nc2i ne n.c2) innerMapping.update(nc2i, remapO(nc1i))
        if((nc1i ne n.c1) || (nc2i ne n.c2)) Set.empty
        else Set(Connection(remapO(n.c1), remapO(n.c2)))
      }
    }
    val outerConns = outer.conns.flatMap(relabelOuter(_))
    val outerPayloadComps = outer.payloadComps.flatMap(relabelOuter(_))
    val relabelInner: Transform = new Transform {
      override def apply(n: EmbArg): EmbArg = n match {
        case EmbArg.Active(0) => c1Temp
        case EmbArg.Active(1) => c2Temp
        case EmbArg.Cell(i) => EmbArg.Cell(i + innerCellOffset)
        case n @ EmbArg.Temp(i, _) => n.copy(i + innerTempOffset)
        case n => n
      }
      override def apply(n: Connection): Set[Connection] = {
        def remap(idx: Idx) = idx match {
          case f: FreeIdx => innerMapping(f)
          case CellIdx(i, p) => CellIdx(i + innerCellOffset, p)
        }
        Set(Connection(remap(n.c1), remap(n.c2)))
      }
    }
    def mapInner(b: BranchWiring): BranchWiring =
      b.copy(
        cellOffset = b.cellOffset + outerCells.length,
        conns = b.conns.flatMap(relabelInner(_)),
        payloadComps = b.payloadComps.flatMap(relabelInner(_)),
        cond = b.cond.flatMap(relabelInner(_)),
        branches = b.branches.map(mapInner),
        tempOffset = b.tempOffset + innerTempOffset,
      )
    val b2 = outer.copy(cells = outerCells, conns = outerConns, payloadComps = outerPayloadComps, branches = inner.branches.map(mapInner))
    (if(b2.branches.length == 1) merge(b2) else b2, outerCellsMapping)
  }

  private[this] def merge(b: BranchWiring): BranchWiring = {
    assert(b.branches.length == 1 && b.branches.head.cellOffset == b.cells.length)
    val ib = b.branches.head
    b.copy(cells = b.cells ++ ib.cells, conns = b.conns ++ ib.conns, payloadComps = b.payloadComps ++ ib.payloadComps, branches = Vector.empty)
  }

  private[this] def tempCount(pcs: Iterable[PayloadComputation]): Int =
    (for {
      pc <- pcs.iterator
      ea <- pc.embArgs.iterator
    } yield { ea match {
      case ea: EmbArg.Temp => ea.idx + 1
      case _ => 0
    }}).maxOption.getOrElse(0)

  // Find unique continuation symbols for a rule plus a list of their eligible cell indices per branch
  private def uniqueContinuationsFor(rule: RuleWiring, rules: scala.collection.Map[RuleKey, RuleWiring]): Set[Symbol] = {
    val funcSym =
      if(rule.derived) null
      else {
        val s = Set(rule.sym1, rule.sym2).filter(_.isDef)
        if(s.size == 1) s.head else null
      }
    if(funcSym != null) {
      val usedSymsByRuleKey = rules.view.filterNot(_._2.derived).mapValues(_.allCreatedCells)
      val symsUsedHere = usedSymsByRuleKey.iterator.filter { case (k, _) => k.sym1 == funcSym || k.sym2 == funcSym }.flatMap(_._2).toSet
      val symsUsedInOtherRules = usedSymsByRuleKey.iterator.filter { case (k, _) => k.sym1 != funcSym && k.sym2 != funcSym }.map { case (k, v) =>
        (k, v.filter(s => s != k.sym1 && s != k.sym2)) // don't count self-recursive calls which can be caused by previous inlining
      } .flatMap(_._2).toSet
      //println(s"funcSym: $funcSym")
      //println(s"symsUsedHere: $symsUsedHere")
      //println(s"symsUsedInOtherRules: $symsUsedInOtherRules")
      (symsUsedHere -- symsUsedInOtherRules).filter(s => (s.isDef || s.isContinuation) && s != funcSym && s.id != "dup" && s.id != "erase")
    } else Set.empty
  }
}
