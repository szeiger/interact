package de.szeiger.interact

import de.szeiger.interact.ast.{CompilationUnit, ShowableNode, Statement, Transform}

import scala.annotation.tailrec
import scala.collection.mutable

/**
 * Inline active pairs on the RHS of rules.
 */
class Inline(global: Global) extends Phase {
  import global._

  def apply(n: CompilationUnit): CompilationUnit = {
    val inlinableRules = n.statements.iterator.collect {
      case r: RulePlan if r.branches.length == 1 && r.sym1.payloadType.isEmpty && r.sym2.payloadType.isEmpty =>
        //TODO inline branches with conditions and merge with parent branches
        //TODO support embedded computations
        (r.key, r)
    }.toMap
    val directInlinable = (for {
      (k, r) <- inlinableRules.iterator
    } yield k -> findInlinable(r.branches.head, inlinableRules).iterator.map(_._3).toVector).toMap
    def verify(r: RulePlan, used: Set[RuleKey], usedList: List[RuleKey]): Unit = {
      if(used.contains(r.key)) error(s"Diverging expansion ${usedList.reverse.map(k => s"($k)").mkString(" => ")}", r.branches.head)
      else {
        val direct = directInlinable.getOrElse(r.key, Vector.empty)
        val subUsed = used + r.key
        val subUsedList = r.key :: usedList
        direct.sortBy(_.pos).foreach { r2 => verify(r2, subUsed, subUsedList) }
      }
    }
    inlinableRules.values.toVector.sortBy(_.pos).foreach(verify(_, Set.empty, Nil))
    checkThrow()

    val proc: Transform = new Transform {
      override def apply(n: Statement): Vector[Statement] = n match {
        case n: RulePlan => super.apply(n)
        case n => Vector(n)
      }
      @tailrec final override def apply(n: BranchPlan): BranchPlan = {
        val pairs = findInlinable(n, inlinableRules)
        if(pairs.isEmpty) n
        else {
          def inlineAll(n: BranchPlan, ps: List[(Int, Int, RulePlan)]): BranchPlan = ps match {
            case (c1, c2, r) :: ps =>
              val (n2, mapping) = inline(n, c1, c2, r)
              inlineAll(n2, ps.map { case (c1, c2, r) => (mapping(c1), mapping(c2), r) })
            case Nil => n
          }
          val newKeys = pairs.map(_._3.key).toSet
          apply(inlineAll(n, pairs.toList))
        }
      }
    }
    proc(n)
  }

  private[this] def findInlinable(n: BranchPlan, rules: Map[RuleKey, RulePlan]): Set[(Int, Int, RulePlan)] =
    n.intConns.iterator.collect { case Connection(CellIdx(c1, -1), CellIdx(c2, -1)) =>
      (c1, c2, rules.get(new RuleKey(n.cells(c1), n.cells(c2))))
    }.collect { case (c1, c2, Some(r)) =>
      if(n.cells(c1) == r.sym1)  (c1, c2, r) else (c2, c1, r)
    }.toSet

  private[this] def inline(b: BranchPlan, c1: Int, c2: Int, r: RulePlan): (BranchPlan, Map[Int, Int]) = {
    //ShowableNode.print(b, name = s"inlining ${r.key} into")
    val ib = r.branches.head
    val outerCellsIndexed = b.cells.iterator.zipWithIndex.filter { case (_, i) => i != c1 && i != c2 }.toVector
    val outerCells = outerCellsIndexed.map(_._1)
    val outerCellsMapping = outerCellsIndexed.iterator.map(_._2).zipWithIndex.map { case (iold, inew) => iold -> inew }.toMap
    val innerMapping = mutable.HashMap.empty[Idx, Idx]
    val relabelOuter: Transform = new Transform {
      override def apply(n: EmbArg): EmbArg = n match {
        case EmbArg.Cell(i) => EmbArg.Cell(outerCellsMapping(i))
        case n => n
      }
      override def apply(n: Connection): Set[Connection] = {
        def remapO(idx: Idx) = idx match {
          case CellIdx(i, p) => CellIdx(outerCellsMapping(i), p)
          case _ => idx
        }
        def remapI(idx: Idx) = idx match {
          case CellIdx(i, p) if i == c1 => FreeIdx(false, p)
          case CellIdx(i, p) if i == c2 => FreeIdx(true, p)
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
    val innerCellOffset = outerCells.length
    val relabelInner: Transform = new Transform {
      override def apply(n: EmbArg): EmbArg = n match {
        case EmbArg.Cell(i) => EmbArg.Cell(i + innerCellOffset)
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
    val b2 = b.copy(cells = outerCells ++ ib.cells,
      conns = b.conns.flatMap(relabelOuter(_)) ++ ib.conns.flatMap(relabelInner(_)),
      payloadComps = b.payloadComps.flatMap(relabelOuter(_)) ++ ib.payloadComps.flatMap(relabelInner(_)))
    (b2, outerCellsMapping)
  }
}