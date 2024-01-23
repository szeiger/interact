package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
 * Check usage of variables and assign payload types to embedded variables. After this phase:
 * - All Apply/ApplyCons constructor calls that need an embedded value contain an Ident
 *   which either refers to an Ident in the pattern or is computed by an EmbeddedExpr.
 * - Implicit creation and copying of labels is made explicit.
 * - PayloadTypes are assigned to all embedded Symbols.
 * - Embedded variable usage is linear.
 * - Embedded expressions are valid assignments and method calls.
 * - Method/operator calls are typed but not yet resolved.
 */
class CleanEmbedded(global: Global) extends Transform with Phase {
  import global._

  override def apply(n: Statement): Vector[Statement] = n match {
    case n: MatchRule => apply(n)
    case n: Let => apply(n)
    case n => Vector(n)
  }

  override def apply(mr: MatchRule): Vector[Statement] = {
    val emb1IdOpt = checkPatternEmbSym(mr.id1, mr.emb1)
    val emb2IdOpt = checkPatternEmbSym(mr.id2, mr.emb2)
    val patternIds = Iterator(emb1IdOpt, emb2IdOpt).flatten.toSet
    patternIds.foreach { _.sym.isPattern = true }
    val branches = mr.branches.map { b =>
      val (reduced2, embRed2) = transformReduction(b.reduced, b.embRed, patternIds)
      val cond2 = b.cond.map(checkCond(_))
      b.copy(cond = cond2, reduced = reduced2, embRed = embRed2)
    }
    Vector(mr.copy(branches = branches))
  }

  override def apply(l: Let): Vector[Statement] = {
    val (es, ees) = transformReduction(l.defs, l.embDefs, Set.empty)
    Vector(l.copy(defs = es, embDefs = ees))
  }

  // check embedded symbol in pattern and assign payload type to is
  private[this] def checkPatternEmbSym(consId: Ident, embId: Option[Ident]): Option[Ident] = {
    val consPT = consId.sym.payloadType
    embId match {
      case s @ Some(id) =>
        assert(id.sym.isDefined)
        id.sym.payloadType = consPT
        if(consPT.isEmpty) {
          error(s"Constructor has no embedded value", consId)
          None
        } else s
      case None =>
        if(consPT.isDefined && !consPT.canErase)
          error(s"Embedded value of type $consPT must be extracted in pattern match", consId)
        None
    }
  }

  // Create new unique embedded symbols in Apply / ApplyCons and assign their PayloadTypes.
  // Ensure that all targets have / do not have embedded symbols based on type.
  // Returns updated exprs, extracted embedded computations, old symbol to new idents mapping, all new symbols
  private[this] def extractConsEmbComps(exprs: Vector[Expr]): (Vector[Expr], Vector[EmbeddedExpr], mutable.HashMap[Symbol, ArrayBuffer[Ident]], Set[Symbol]) = {
    val local = new SymbolGen("$e$", isEmbedded = true)
    val symbolMap = mutable.HashMap.empty[Symbol, ArrayBuffer[Ident]]
    val newEmbComps = Vector.newBuilder[EmbeddedExpr]
    val defaultCreate = ArrayBuffer.empty[Symbol]
    val allEmbCompSyms = Set.newBuilder[Symbol]
    val proc: Transform = new Transform {
      def tr[T <: AnyApply](n: T): T = {
        val emb2 = n.embedded match {
          case s @ Some(e) =>
            if(n.target.sym.payloadType.isEmpty)
              error("Constructor has no embedded value", e)
            val prefix = e match {
              case i: Ident => i.s
              case _ => n.target.sym.id
            }
            val id = local.id(isEmbedded = true, payloadType = n.target.sym.payloadType, prefix = prefix).setPos(e.pos)
            e match {
              case oldId: Ident if !oldId.sym.isPattern =>
                symbolMap.getOrElseUpdate(oldId.sym, ArrayBuffer.empty) += id
              case _ =>
                newEmbComps += EmbeddedAssignment(id, e)
                allEmbCompSyms += id.sym
            }
            Some(id)
          case None if n.target.sym.payloadType.canCreate =>
            val id = local.id(isEmbedded = true, payloadType = n.target.sym.payloadType, prefix = "cr_"+n.target.sym.id).setPos(n.pos)
            defaultCreate += id.sym
            allEmbCompSyms += id.sym
            Some(id)
          case None =>
            if(n.target.sym.payloadType.isDefined)
              error(s"Embedded value of type ${n.target.sym.payloadType} must be created", n)
            None
        }
        n.copy(embedded = emb2).asInstanceOf[T]
      }
      override def apply(n: Apply): Apply = tr(super.apply(n))
      override def apply(n: ApplyCons): ApplyCons = tr(super.apply(n))
    }
    val exprs2 = exprs.map(proc(_))
    if(defaultCreate.nonEmpty)
      newEmbComps += CreateLabels(local(isEmbedded = true, payloadType = PayloadType.REF, prefix = "defCr"), defaultCreate.toVector)
    (exprs2, newEmbComps.result(), symbolMap, allEmbCompSyms.result())
  }

  private[this] def checkCond(cond: EmbeddedExpr): EmbeddedExpr = {
    val proc: Transform = new Transform {
      override def apply(n: Ident): Ident = {
        if(n.sym.isDefined && !n.sym.isPattern)
          error("Unknown symbol (not in pattern)", n)
        n
      }
    }
    proc(cond)
  }

  private[this] def checkLinearity(patternIds: Iterable[Ident], consIds: Iterable[Ident], usageCount: mutable.HashMap[Symbol, Int]): Unit = {
    patternIds.foreach { id =>
      val pt = id.sym.payloadType
      usageCount(id.sym) match {
        case 0 => if(!pt.canErase) error(s"Cannot implicitly erase value of type $pt", id)
        case 1 =>
        case _ => if(!pt.canCopy) error(s"Cannot implicitly copy value of type $pt", id)
      }
    }
    consIds.foreach { id =>
      val pt = id.sym.payloadType
      usageCount(id.sym) match {
        case 0 => if(!pt.canCreate) error(s"Cannot implicitly create value of type $pt", id)
        case 1 =>
        case _ => error(s"Duplicate assignment", id)
      }
    }
  }

  private[this] def transformReduction(reduced: Vector[Expr], embComps: Vector[EmbeddedExpr],
    patternIds: Set[Ident]): (Vector[Expr], Vector[EmbeddedExpr]) = {
    val (reduced2, newEmbComps, newEmbIds, assignedEmbCompSyms) = extractConsEmbComps(reduced)
    val allEmbCompSyms = assignedEmbCompSyms ++ newEmbIds.values.flatten.map(_.sym)
    val usageCount = mutable.HashMap.from((patternIds.map(_.sym) ++ allEmbCompSyms).map((_ , 0)))
    def checkLHS(i: Ident): Unit =
      if(!allEmbCompSyms.contains(i.sym)) error("Assignment must be to an embedded variable of the reduction", i)
    val mapIdents: Transform = new Transform {
      override def apply(n: Ident): Ident = {
        if(n.sym.isCons || n.sym.isEmpty) n
        else {
          val n2 = newEmbIds.get(n.sym) match {
            case Some(ids) if ids.length > 1 =>
              error(s"Multiple occurrences of symbol ${n.sym} in cell constructors", n)
              n
            case Some(ids) => ids.head
            case _ => n
          }
          if (!n2.sym.isPattern && !allEmbCompSyms.contains(n2.sym)) {
            error("Unknown symbol (not in pattern or cell constructor)", n)
            n
          }
          usageCount.update(n2.sym, usageCount(n2.sym) + 1)
          n2
        }
      }
      override def apply(n: EmbeddedAssignment): EmbeddedAssignment = {
        val n2 = super.apply(n)
        checkLHS(n2.lhs)
        n2
      }
    }
    val mappedEmbComps = ArrayBuffer.empty[EmbeddedExpr]
    embComps.foreach(mappedEmbComps += mapIdents(_))
    newEmbComps.foreach(mappedEmbComps += mapIdents(_))
    val unusedNewEmbIds =
      newEmbIds.iterator.map { case (oldSym, newIds) => (oldSym, newIds.filter(i => usageCount(i.sym) == 0)) }.filter(_._2.nonEmpty).toVector
    unusedNewEmbIds.foreach { case (oldSym, newIds) =>
      mappedEmbComps += CreateLabels(oldSym, newIds.iterator.map(_.sym).toVector).setPos(newIds.head.pos)
      newIds.foreach { i => usageCount.update(i.sym, usageCount(i.sym) + 1) }
    }
    checkLinearity(patternIds, newEmbIds.iterator.flatMap(_._2).toVector, usageCount)

//    println("************* Reduction:")
//    mappedEmbComps.foreach(ShowableNode.print(_))
//    println("newEmbIds: " + newEmbIds.iterator.map { case (k, v) => s"$k -> ${v.mkString("[", ",", "]")}"}.mkString(", "))
//    println("unusedNewEmbIds: " + unusedNewEmbIds.iterator.map { case (k, v) => s"$k -> ${v.mkString("[", ",", "]")}"}.mkString(", "))
//    println("usageCount: " + usageCount.iterator.map { case (k, v) => s"$k -> $v"}.mkString(", "))

    (reduced2, mappedEmbComps.toVector)
  }
}
