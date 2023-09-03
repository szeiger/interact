package de.szeiger.interact

import de.szeiger.interact.ast._

/**
 * Create curried and derived rules, and remove all Cons and Def statements.
 */
class Curry(global: Global) extends Transform with Phase {
  import global._

  private[this] lazy val defaultDeriveSyms =
    defaultDerive.iterator.map(globalSymbols.get).filter(_.exists(_.isCons)).map(_.get).toVector

  private[this] def derivedRules(syms1: Vector[Symbol], sym2: Symbol, pos: Position): Vector[DerivedRule] =
    syms1.flatMap { sym =>
      if(sym.id == "erase" || sym.id == "dup") Vector(DerivedRule(sym, sym2).setPos(pos))
      else { error(s"Don't know how to derive '$sym'", pos); Vector.empty }
    }

  private[this] def singleNonIdentIdx(es: Seq[Expr]): Int = {
    val i1 = es.indexWhere(e => !e.isInstanceOf[Ident])
    if(i1 == -1) -1
    else {
      val i2 = es.lastIndexWhere(e => !e.isInstanceOf[Ident])
      if(i2 == i1) i1 else -2
    }
  }

  private[this] def createCurriedDef(lid: Ident, rid: Ident, idx: Int, rhs: Boolean, at: Position): (Ident, Vector[CheckedRule]) = {
    val ls = lid.sym
    val rs = rid.sym
    val curryId = Ident(s"${ls.id}$$${if(rhs) "ac" else "nc"}$$${rs.id}").setPos(lid.pos)
    val rules = globalSymbols.get(curryId) match {
      case Some(sym) =>
        if(sym.matchContinuationPort != idx) error(s"Port mismatch in curried ${ls.id} -> ${rs.id} match", at)
        curryId.sym = sym
        Vector.empty
      case None if ls.hasPayload && rs.hasPayload =>
        error("Implementation limitation: Curried definitions cannot have payload on both sides", at)
        Vector.empty
      case None =>
        val curriedPtp = if(ls.hasPayload) ls.payloadType else rs.payloadType
        val emb1 = if(ls.hasPayload) Some(mkLocalId("$l").setPos(lid.pos)) else None
        val emb2 = if(rs.hasPayload) Some(mkLocalId("$r").setPos(rid.pos)) else None
        curryId.sym = globalSymbols.define(curryId.s, isCons = true, arity = ls.arity + rs.arity - 1, payloadType = curriedPtp, matchContinuationPort = idx)
        val largs = (0 until ls.callArity).map(i => mkLocalId(s"$$l$i")).toVector
        val rargs = (0 until rs.callArity).map(i => mkLocalId(s"$$r$i")).toVector
        val (keepArgs, splitArgs) = if(rhs) (rargs, largs) else (largs, rargs)
        val curryArgs = keepArgs ++ splitArgs.zipWithIndex.filter(_._2 != idx).map(_._1)
        val der = derivedRules(defaultDeriveSyms, curryId.sym, Position.unknown)
        val fwd = Assignment(Apply(curryId, emb1.orElse(emb2), curryArgs), splitArgs(idx))
        der :+ MatchRule(lid, rid, largs, rargs, emb1, emb2, Vector(Branch(None, Vector.empty, Vector(fwd)).setPos(at))).setPos(at)
    }
    (curryId, rules)
  }

  private[this] def curry(mr: MatchRule): Vector[Statement] = mr.args1.indexWhere(e => !e.isInstanceOf[Ident]) match {
    case -1 =>
      singleNonIdentIdx(mr.args2) match {
        case -2 =>
          error(s"Only one nested match allowed", mr.pos)
          Vector.empty
        case -1 =>
          mr.args1.toSet.intersect(mr.args2.toSet).foreach { case i: Ident =>
            error(s"Duplicate variable '${i.s}' on both sides of a match", i)
          }
          Vector(mr)
        case idx =>
          val (curryId, curryRules) = createCurriedDef(mr.id1, mr.id2, idx, false, mr.pos)
          val ApplyCons(cid, cemb, crargs) = mr.args2(idx)
          val clargs = mr.args1 ++ mr.args2.zipWithIndex.filter(_._2 != idx).map(_._1.asInstanceOf[Ident])
          curryRules ++ curry(MatchRule(curryId, cid, clargs, crargs, mr.emb1.orElse(mr.emb2), cemb, mr.reduction).setPos(mr.pos))
      }
    case idx =>
      val (curryId, curryRules) = createCurriedDef(mr.id1, mr.id2, idx, true, mr.pos)
      val ApplyCons(cid, cemb, clargs) = mr.args1(idx)
      val crargs = mr.args2 ++ mr.args1.zipWithIndex.filter(_._2 != idx).map(_._1.asInstanceOf[Ident])
      curryRules ++ curry(new MatchRule(curryId, cid, crargs, clargs, mr.emb1.orElse(mr.emb2), cemb, mr.reduction).setPos(mr.pos))
  }

  override def apply(n: Statement): Vector[Statement] = n match {
    case n: MatchRule => curry(n)
    case c: Cons => derivedRules(c.der.map(_.map(_.sym)).getOrElse(defaultDeriveSyms), c.name.sym, c.name.pos)
    case d: Def =>
      val erase = DerivedRule(globalSymbols("erase"), d.name.sym).setPos(d.name.pos)
      lazy val dup = DerivedRule(globalSymbols("dup"), d.name.sym).setPos(d.name.pos)
      if(d.name.s != "dup" && d.name.s != "erase") Vector(erase, dup) else Vector(erase)
    case n => Vector(n)
  }
}