package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable

/**
 * Check usage of variables and assign payload types to embedded variables.
 */
class CheckVariables(global: Global) extends Phase {
  import global._

  def apply(n: CompilationUnit): CompilationUnit = {
    n.statements.foreach(check)
    n
  }

  private[this] def check(n: Statement): Unit = n match {
    case n: MatchRule => checkMatchRule(n)
    case n: Let => checkLet(n)
    case _ =>
  }

  private[this] def checkMatchRule(mr: MatchRule): Unit = {
    val rm = new RefsMap
    mr.args1.foreach(rm.collect)
    mr.args2.foreach(rm.collect)
    mr.emb1.foreach(rm.collect)
    mr.emb2.foreach(rm.collect)
    val (emb1Sym, emb1Id) = patternEmbSym(mr.id1, mr.emb1)
    val (emb2Sym, emb2Id) = patternEmbSym(mr.id2, mr.emb2)
    val patSyms = rm.allSymbols.toSet
    mr.reduction.foreach { b =>
      val refs = rm.sub()
      refs.collect(b)
      if(refs.hasError) {
        val nonEmbErrs = refs.err.filter(!_.isEmbedded)
        if(nonEmbErrs.nonEmpty)
          error(s"Non-linear use of variable(s) ${nonEmbErrs.map(s => s"'$s'").mkString(", ")}", b)
      }
      b.cond.foreach { cond =>
        val condSyms = new RefsMap
        condSyms.collect(cond)
        val newSyms = condSyms.allSymbols.filter(s => !patSyms.contains(s)).toSet
        if(newSyms.nonEmpty)
          error(s"Variable(s)s ${newSyms.map(s => s"'$s'").mkString(", ")} in condition do not refer to pattern", cond)
      }
      val patPayloads = mutable.HashMap.empty[Symbol, Position]
      if(emb1Sym.isDefined) patPayloads.put(emb1Sym, emb1Id.get.pos)
      if(emb2Sym.isDefined) patPayloads.put(emb2Sym, emb2Id.get.pos)
      checkReduction(b.reduced, b.embRed, patPayloads)
    }
  }

  private[this] def checkLet(l: Let): Unit = {
    checkReduction(l.defs, l.embDefs, mutable.HashMap.empty)
  }

  private[this] def checkReduction(es: Vector[Expr], ees: Vector[EmbeddedExpr],
    patPayloads: mutable.HashMap[Symbol, Position]): Unit = {
    val applies = es.flatMap(e => findApplies(e))
    val payloads = mutable.HashMap.from(patPayloads)
    applies.foreach {
      case (i, Some(ei: Ident)) =>
        val pt = i.sym.payloadType
        payloads.get(ei.sym) match {
          case Some(_) =>
            if(ei.sym.payloadType != pt) error(s"Inconsistent type for embedded variable: $pt != ${ei.sym.payloadType}", i)
          case None =>
            payloads.put(ei.sym, ei.pos)
            assert(ei.sym.payloadType.isEmpty)
            ei.sym.payloadType = pt
        }
      case (i, None) =>
        if(i.sym.payloadType.isDefined && i.sym.payloadType != PayloadType.LABEL)
          error(s"Embedded value of type ${i.sym.payloadType} must be specified", i)
      case _ =>
    }
    val refs = new RefsMap
    patPayloads.keysIterator.foreach(refs.inc)
    val defs = mutable.HashMap.empty[Symbol, Ident]
    val allIds, createdIds = mutable.ArrayBuffer.empty[Ident]
    applies.foreach {
      case (_, Some(ee)) => findEmbIds(ee, allIds, createdIds)
      case _ =>
    }
    ees.foreach(findEmbIds(_, allIds, createdIds))
    val createdSyms = createdIds.iterator.map(_.sym).toSet
    allIds.foreach { ei =>
      if(!payloads.contains(ei.sym))
        error(s"Cannot determine type of embedded variable ${ei.sym}", ei)
      else refs.inc(ei.sym)
      defs.put(ei.sym, ei)
    }
    payloads.foreach { case (s, pos) =>
      val r = refs(s)
      val pt = s.payloadType
      if(!pt.canCopy && r > 2)
        error(s"Cannot copy embedded value of type $pt", pos)
      else if(!pt.canCreate && !patPayloads.keySet.contains(s) && !createdSyms.contains(s))
        error(s"Cannot create embedded value of type $pt", pos)
      else if(!pt.canErase && r < 2)
        error(s"Cannot erase embedded value of type $pt", pos)
    }
  }

  private[this] def findEmbIds(n: EmbeddedExpr, allIds: mutable.ArrayBuffer[Ident],
    createdIds: mutable.ArrayBuffer[Ident]): Unit = {
    def f(n: EmbeddedExpr): Unit = n match {
      case n: Ident => allIds += n
      case EmbeddedApply(_, args, _) => args.iterator.foreach {
        case i: Ident =>
          allIds += i
          createdIds += i
        case e => f(e)
      }
      case _ =>
    }
    f(n)
  }

  private[this] def findApplies(n: Node): Iterator[(Ident, Option[EmbeddedExpr])] = n match {
    case Apply(t, emb, args) => Iterator.single((t, emb)) ++ args.flatMap(findApplies)
    case ApplyCons(t, emb, args) => Iterator.single((t, emb)) ++ args.flatMap(findApplies)
    case n: Expr => n.nodeChildren.flatMap(findApplies)
    case n => Iterator.empty
  }

  private[this] def patternEmbSym(consId: Ident, o: Option[EmbeddedExpr]): (Symbol, Option[Ident]) = {
    val embId = o match {
      case o @ Some(i: Ident) => o.asInstanceOf[Some[Ident]]
      case Some(e) =>
        error(s"Embedded expression in pattern match must be a variable", e)
        None
      case _ => None
    }
    val embSym = embId.map(_.sym).getOrElse(Symbol.NoSymbol)
    val consPT = consId.sym.payloadType
    if(consPT.isDefined && embSym.isEmpty && !consPT.canErase)
      error(s"Embedded value of type $consPT must be extracted in pattern match", consId)
    else if(embSym.isDefined) {
      if(consPT.isEmpty)
        error(s"Constructor has no embedded value", consId)
      else embSym.payloadType = consPT
    }
    (embSym, embId)
  }
}
