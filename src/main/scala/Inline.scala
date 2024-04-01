package de.szeiger.interact

import de.szeiger.interact.ast.{CompilationUnit, RuleKey, ShowableNode, Statement, Symbol, Transform}

import scala.annotation.tailrec
import scala.collection.mutable

/**
 * Inline active pairs on the RHS of rules and combine initial rules
 */
class Inline(val global: Global) extends Phase {
  import global._

  def apply(n: CompilationUnit): CompilationUnit = {
    val allRules = n.statements.iterator.collect { case r: RuleWiring => (r.key, r) }.toMap
    val rulesBySym = allRules.toVector.flatMap { case (k, r) => Vector((k.sym1, r), (k.sym2, r)) }.groupBy(_._1).map { case (k, v) => (k, v.map(_._2)) }
    val fullyInlinableRules = allRules.filter { case (_, r) => r.branches.length == 1 && (config.backend.allowPayloadTemp || (r.sym1.payloadType.isEmpty && r.sym2.payloadType.isEmpty)) }
    val uniqueContSyms: Map[RuleKey, Set[Symbol]] =
      if(config.backend.inlineUniqueContinuations && config.inlineUniqueContinuations) {
        val fwd = allRules.iterator.collect { case (_, r) => (r, uniqueContinuationsFor(r, allRules)) }.toVector
        val rev = fwd.flatMap { case (r, syms) =>
          val f = funcSymFor(r)
          if(f.isEmpty) Vector.empty
          else syms.iterator.flatMap(s => rulesBySym.getOrElse(s, Vector.empty)).map(r => (r.key, r.branches.flatMap(_.cells).filter(_ == f.get).toSet))
        }
        (fwd.map { case (r, syms) => (r.key, syms) } ++ rev).toMap
      } else Map.empty
    checkCircular(fullyInlinableRules)

    val initial = mutable.ArrayBuffer.empty[InitialRuleWiring]
    val st2 = Vector.newBuilder[Statement]
    n.statements.foreach {
      case r: RuleWiring => st2 += inlineRec(r, Nil, SymCounts.empty, SymCounts.empty, uniqueContSyms, allRules)
      case r: InitialRuleWiring => initial += r
      case s => s
    }
    st2 += mergeInitial(initial)
    n.copy(st2.result())
  }

  private[this] def mergeInitial(rs: mutable.ArrayBuffer[InitialRuleWiring]): InitialRuleWiring = {
    if(rs.length == 1) rs.head
    else {
      val free = rs.toVector.flatMap(_.free)
      val cells = Vector.newBuilder[Symbol]
      val conns = Set.newBuilder[Connection]
      val payloadComps = Vector.newBuilder[PayloadComputation]
      var statSteps = 0
      var cellOffset, freeOffset = 0
      val relabel: Transform = new Transform {
        override def apply(n: EmbArg): EmbArg = n match {
          case EmbArg.Cell(i) => EmbArg.Cell(i + cellOffset)
          case n => n
        }
        override def apply(n: Connection): Set[Connection] = {
          def remap(idx: Idx) = idx match {
            case CellIdx(i, p) => CellIdx(i + cellOffset, p)
            case FreeIdx(0, p) => FreeIdx(0, p + freeOffset)
            case _ => idx
          }
          val nc1 = remap(n.c1)
          val nc2 = remap(n.c2)
          if((nc1 eq n.c1) && (nc2 eq n.c2)) Set(n)
          else Set(n.copy(nc1, nc2))
        }
      }
      rs.foreach { r =>
        val b = r.branch
        assert(b.cellOffset == 0)
        assert(b.branches.isEmpty)
        assert(b.cond.isEmpty)
        assert(b.tempOffset == 0)
        cells ++= b.cells
        statSteps += b.statSteps
        if(cellOffset == 0 && freeOffset == 0) {
          conns ++= b.conns
          payloadComps ++= b.payloadComps
        } else {
          conns ++= b.conns.flatMap(relabel(_))
          payloadComps ++= b.payloadComps.flatMap(relabel(_))
        }
        cellOffset += b.cells.length
        freeOffset += r.free.length
      }
      InitialRuleWiring(free, BranchWiring(0, cells.result(), conns.result(), payloadComps.result(), None, Vector.empty, 0, statSteps))
    }
  }

  private[this] def inlineRec(r: RuleWiring, parents: List[RuleKey], parentAvailable: SymCounts, parentCreated: SymCounts,
    uniqueContSyms: Map[RuleKey, Set[Symbol]], allRules: Map[RuleKey, RuleWiring]): RuleWiring = {
    val chain = r.key :: parents
    val prefix = "    " * (parents.length+1)
    phaseLog(s"${prefix}Inlining into ${r.key}")
    phaseLog(r, "Inline target", prefix+"  ")
    val ruleAvailable = parentAvailable ++ Vector(r.sym1, r.sym2).filterNot(_.isSingleton)
    val uniqueConts = uniqueContSyms.getOrElse(r.key, Set.empty)
    val branches2 = Transform.flatMapC(r.branches) { branch =>
      val branchCreated = parentCreated ++ branch.cells.filterNot(_.isSingleton)
      phaseLog(s"$prefix  create ${branchCreated -- ruleAvailable}")

      // direct
      val possiblePairs = findInlinableActivePairs(branch, allRules).filter { case (_, _, r2) =>
        !chain.contains(r2.key) || (config.inlineFullAll && r2.branches.length == 1)
      }
      val possiblePairsRecInlined = possiblePairs.map { case (i1, i2, r2) =>
        phaseLog(s"$prefix  direct simple: ${r2.key}")
        (i1, i2, inlineRec(r2, chain, ruleAvailable, branchCreated, uniqueContSyms, allRules))
      }.filter { case (_, _, r2) =>
        // filter again because inlining could have produced more branches
        !chain.contains(r2.key) || (config.inlineFullAll && r2.branches.length == 1)
      }
      val (simple, branching) = possiblePairsRecInlined.toList.partition(_._3.branches.length == 1)
      val simpleFiltered =
        if(!config.inlineFull) Nil
        else if(config.backend.allowPayloadTemp) simple
        else simple.filter { case (_, _, r2) => r2.sym1.payloadType.isEmpty && r2.sym2.payloadType.isEmpty }
      val direct = simpleFiltered ++
        (if(config.inlineBranching && config.backend.inlineBranching) branching.take(1) else Nil) //TODO inline multiple branching rules?
      phaseLog(s"$prefix  Direct inlining ${direct.length} RuleWirings")
      direct.foreach { case (i1, i2, rw) => phaseLog(rw, s"Direct inlining at ($i1, $i2)", prefix+"  ") }
      val branch2 = inlineAll(branch, direct, prefix + "  ")
      if(branch2 eq branch) phaseLog(s"$prefix  Direct inlined (no change)")
      else phaseLog(branch2, "Direct inlined", prefix+"  ")

      // speculative
      if(uniqueConts.nonEmpty && branch2.cond.isEmpty && branch2.branches.isEmpty) { //TODO inline into already branching rule? Create nested conditions?
        val candidates = branch2.cells.iterator.zipWithIndex.flatMap {
          case (s, i) if uniqueConts.contains(s) && !ruleAvailable.contains(s) =>
            branch2.principalConns(i) match {
              case f: FreeIdx => Iterator.single((s, i, f))
              case _ => Iterator.empty
            }
          case _ => Iterator.empty
        }.toSet
        val candidate = candidates.headOption //TODO choose the best candidate or inline multiple ones?
        val candidateRecInlined = candidate.map { case (usym, _, _) =>
          val partners = allRules.iterator.filterNot(_._2.derived).collect {
            case (k, r) if k.sym1 == usym => (k.sym2, r)
            case (k, r) if k.sym2 == usym => (k.sym1, r)
          }.toVector.filter { case (s, r) => !chain.contains(r.key) }
          phaseLog(s"$prefix  cont: $usym")
          partners.map { case (psym, r2) =>
            (psym, inlineRec(r2, chain, ruleAvailable + psym, branchCreated, uniqueContSyms, allRules))
          }
        }

        val branches3 = (candidate, candidateRecInlined) match {
          case (Some((usym, idx, wire)), Some(partners)) if partners.nonEmpty =>
            //ShowableNode.print(branch2, name = "Original branch")
            partners.map { case (psym, prule) =>
              //phaseLog(s"Activating branch of ${rule.key} with ($idx, $usym, $psym, $wire):")
              val b = makeActive(branch2, psym, wire)
              val (c1, c2) = if(prule.key.sym1 == usym) (idx, b.cells.length-1) else (b.cells.length-1, idx)
              assert(b.branches.isEmpty)
              //ShowableNode.print(b, name = s"Inlining into at $c1, $c2")
              //ShowableNode.print(prule, name = "Inlining")
              val b2 = inline(b, c1, c2, prule, prefix+"  ")._1
              //ShowableNode.print(b2, name = "Activated")
              b2
            } :+ branch2
          case _ => Vector(branch2)
        }
        branches3.foreach(b => phaseLog(b, "Speculative inlined", prefix+"  "))
        branches3
      } else {
        phaseLog(s"$prefix  Speculative inlined (no change)")
        Vector(branch2)
      }
    }
    val res = if(branches2 eq r.branches) r else r.copy(branches = branches2)
    phaseLog(s"${prefix}Inlining into ${r.key} finished")
    //branches2.foreach(_.validate())
    res
  }

  private[this] def findInlinableActivePairs(n: BranchWiring, rules: Map[RuleKey, RuleWiring]): Set[(Int, Int, RuleWiring)] =
    n.intConns.iterator.collect { case Connection(CellIdx(c1, -1), CellIdx(c2, -1)) =>
      (c1, c2, rules.get(new RuleKey(n.cells(c1), n.cells(c2))))
    }.collect { case (c1, c2, Some(r)) =>
      if(n.cells(c1) == r.sym1)  (c1, c2, r) else (c2, c1, r)
    }.toSet

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

  @tailrec
  private[this] def inlineAll(n: BranchWiring, ps: List[(Int, Int, RuleWiring)], prefix: String): BranchWiring = ps match {
    case (c1, c2, r) :: ps =>
      val (n2, mapping) = inline(n, c1, c2, r, prefix)
      inlineAll(n2, ps.map { case (c1, c2, r) => (mapping(c1), mapping(c2), r) }, prefix)
    case Nil => n
  }

  private[this] def checkCircular(inlinableRules: Map[RuleKey, RuleWiring]): Unit = {
    val directInlinable = (for {
      (k, r) <- inlinableRules.iterator
    } yield k -> findInlinableActivePairs(r.branches.head, inlinableRules).iterator.map(_._3).toVector).toMap

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

  private[this] def inline(outer: BranchWiring, c1: Int, c2: Int, inner: RuleWiring, prefix: String): (BranchWiring, Map[Int, Int]) = {
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
    var foundLocalCheckPrincipal = false
    val relabelInner: Transform = new Transform {
      override def apply(n: EmbArg): EmbArg = n match {
        case EmbArg.Active(0) => c1Temp
        case EmbArg.Active(1) => c2Temp
        case EmbArg.Cell(i) => EmbArg.Cell(i + innerCellOffset)
        case n @ EmbArg.Temp(i, _) => n.copy(i + innerTempOffset)
        case n => n
      }
      def remap(idx: Idx) = idx match {
        case f: FreeIdx => innerMapping(f)
        case CellIdx(i, p) => CellIdx(i + innerCellOffset, p)
      }
      override def apply(n: Connection): Set[Connection] = Set(Connection(remap(n.c1), remap(n.c2)))
      override def apply(n: CheckPrincipal) = {
        val w2 = remap(n.wire)
        if(w2 eq n.wire) n
        else {
          if(w2.isInstanceOf[CellIdx]) foundLocalCheckPrincipal = true
          n.copy(wire = w2)
        }
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
    phaseLog(b2, s"Inlined at ($c1, $c2)", prefix)

    val b3 = if(foundLocalCheckPrincipal) resolveCheckPrincipal(b2) else b2

    (if(b3.branches.length == 1) {
      val res = merge(b3)
      phaseLog(res, s"Merged", prefix)
      res
    } else {
      phaseLog(s"${prefix}Merged: No change")
      b3
    }, outerCellsMapping)
  }

  // resolve CheckPrincipal(CellIdx(...)) statically
  private[this] def resolveCheckPrincipal(b: BranchWiring): BranchWiring = {
    val tr = new Transform {
      override def apply(n: BranchWiring) = {
        val branches2 = n.branches.flatMap { br =>
          br.cond match {
            case Some(CheckPrincipal(CellIdx(c1, p1), sym, ac)) =>
              if(p1 >= 0) {
                Vector.empty
              } else {
                //TODO: Can we end up with a principal connection here?
                ???
              }
            case _ => Vector(apply(br))
          }
        }
        n.copy(branches = branches2)
      }
    }
    tr(b)
  }

  private[this] def merge(b: BranchWiring): BranchWiring = {
    assert(b.branches.length == 1 && b.branches.head.cellOffset == b.cells.length)
    val ib = b.branches.head
    b.copy(cells = b.cells ++ ib.cells, conns = b.conns ++ ib.conns, payloadComps = b.payloadComps ++ ib.payloadComps, branches = ib.branches)
  }

  private[this] def tempCount(pcs: Iterable[PayloadComputation]): Int =
    (for {
      pc <- pcs.iterator
      ea <- pc.embArgs.iterator
    } yield { ea match {
      case ea: EmbArg.Temp => ea.idx + 1
      case _ => 0
    }}).maxOption.getOrElse(0)

  private[this] def funcSymFor(rule: RuleWiring): Option[Symbol] =
    if(rule.derived) None
    else {
      val s = Set(rule.sym1, rule.sym2).filter(_.isDef)
      if(s.size == 1) s.headOption else None
    }

  // Find unique continuation symbols for a rule
  private[this] def uniqueContinuationsFor(rule: RuleWiring, rules: scala.collection.Map[RuleKey, RuleWiring]): Set[Symbol] = {
    val funcSym = funcSymFor(rule).orNull
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
