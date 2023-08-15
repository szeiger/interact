package de.szeiger.interact

import de.szeiger.interact.ast._

/**
 * Complete rules by synthesizing omitted return wires in conditions and reductions.
 */
class ExpandRules(global: Global) extends Transform with Phase {
  import global._

  val normalize = new Normalize(global)

  private[this] def wildcardCount(e: Expr): Int = e match {
    case _: Wildcard => 1
    case e: Apply => e.args.iterator.map(wildcardCount).sum
    case _ => 0
  }

  private[this] def returnArity(e: Expr): Int = e match {
    case e: Apply => e.target.sym.returnArity
    case Assignment(lhs, rhs) => wildcardCount(lhs) + wildcardCount(rhs)
    case _ => 0
  }

  override def apply(n: Statement): Vector[Statement] = n match {
    case n: Match => apply(n)
    case n: Def => apply(n)
    case n => Vector(n)
  }

  override def apply(m: Match): Vector[Statement] = returnArity(m.on.head) match {
    case 0 => checkedMatch(m.on, m.reduced, m.pos)
    case n =>
      assert(m.on.length == 1)
      val p = m.on.head.pos
      checkedMatch(Vector(Assignment(m.on.head, Tuple((1 to n).map(i => mkLocalId(s"$$ret$i").setPos(p)).toVector).setPos(p)).setPos(p)), m.reduced, m.pos)
  }

  override def apply(d: Def): Vector[Statement] = {
    d.copy(rules = Vector.empty).setPos(d.pos) +: d.rules.flatMap { r =>
      val dret = Tuple(d.ret).setPos(d.pos)
      checkedMatch(Vector(Assignment(Apply(d.name, d.embeddedId, r.on ++ d.args.drop(r.on.length)).setPos(d.pos), dret).setPos(r.pos)), r.reduced, r.pos)
    }
  }

  private[this] def connectLastStatement(e: Expr, extraRhs: Vector[Ident]): Expr = e match {
    case e: Assignment => e
    case e: Tuple =>
      if(e.exprs.length != extraRhs.length)
        error(s"Expected return arity ${extraRhs.length} for reduction but got ${e.exprs.length}", e)
      Assignment(Tuple(extraRhs).setPos(extraRhs.head.pos), e).setPos(extraRhs.head.pos)
    case e: Apply =>
      val sym = globalSymbols(e.target.s)
      if(sym.returnArity == 0) e
      else {
        if(sym.returnArity != extraRhs.length)
          error(s"Expected return arity ${extraRhs.length} for reduction but got ${sym.returnArity}", e)
        Assignment(if(extraRhs.length == 1) extraRhs.head else Tuple(extraRhs).setPos(extraRhs.head.pos), e).setPos(extraRhs.head.pos)
      }
    case e: NatLit =>
      if(extraRhs.length != 1)
        error(s"Expected return arity ${extraRhs.length} for reduction but got 1", e)
      Assignment(extraRhs.head, e).setPos(extraRhs.head.pos)
    case e: Ident =>
      if(extraRhs.length != 1)
        error(s"Expected return arity ${extraRhs.length} for reduction but got 1", e)
      Assignment(extraRhs.head, e).setPos(e.pos)
  }

  private[this] def checkedMatch(on: Vector[Expr], red: Vector[Branch], pos: Position): Vector[Statement] = {
    val inlined = normalize.toInline(normalize.toANF(on).map(normalize.toConsOrder))
    inlined match {
      case Seq(Assignment(ApplyCons(lid, lemb, largs: Seq[Expr]), ApplyCons(rid, remb, rargs))) =>
        val compl = if(lid.sym.isDef) largs.takeRight(lid.sym.returnArity) else Vector.empty
        val connected = red.map { r =>
          r.copy(reduced = r.reduced.init :+ connectLastStatement(r.reduced.last, compl.asInstanceOf[Vector[Ident]])).setPos(r.pos)
        }
        Vector(MatchRule(lid.sym, rid.sym, largs, rargs, lemb.map(_.asInstanceOf[Ident]), remb.map(_.asInstanceOf[Ident]), connected).setPos(pos))
      case _ =>
        error(s"Invalid match", pos)
        Vector.empty
    }
  }
}
