package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable

// Normalize expressions:
// - all compound expressions are unnested (ANF)
// - constructor Idents are converted to Ap
// - only non-constructor Idents can be nested
// - all Ap assignments have the Ap on the RHS
// - all direct assignments are untupled
// - wildcards in assignments are resolved
// - only the last expr can be a non-assignment
class Normalize(global: Global) {
  import global._

  private var lastTmp = 0
  private def mk(): Ident = { lastTmp += 1; mkLocalId(s"$$u${lastTmp}") }

  def toANF(exprs: Seq[Expr]): Seq[Expr] = {
    val assigned = mutable.HashSet.empty[Ident]
    val buf = mutable.ArrayBuffer.empty[Expr]
    def expandWildcards(e: Expr, wild: Ident): Expr = e match {
      case Assignment(ls, rs) =>
        val wild2 = mk()
        val ass2 = Assignment(expandWildcards(ls, wild2), expandWildcards(rs, wild2)).setPos(e.pos)
        if(assigned.contains(wild2)) { reorder(unnest(ass2, false)); wild2 }
        else ass2
      case Tuple(es) => Tuple(es.map(expandWildcards(_, wild))).setPos(e.pos)
      case Apply(t, emb, args) => Apply(t, emb, args.map(expandWildcards(_, wild))).setPos(e.pos)
      case Wildcard() =>
        if(assigned.contains(wild)) error(s"Duplicate wildcard in assignment", e)
        assigned += wild
        wild.setPos(e.pos)
      case e: Ident => e
    }
    def unnest(e: Expr, nested: Boolean): Expr = e match {
      case Assignment(ls, rs) =>
        if(nested) error("Unexpected nested assignment without wilcard", e)
        Assignment(unnest(ls, false), unnest(rs, false)).setPos(e.pos)
      case Tuple(es) => Tuple(es.map(unnest(_, true))).setPos(e.pos)
      case IdentOrAp(id, emb, args) =>
        if(id.sym.isCons || args.nonEmpty) {
          val ap = Apply(id, emb, args.map(unnest(_, true))).setPos(e.pos)
          if(nested) {
            val v = mk().setPos(e.pos)
            reorder(Assignment(v, ap).setPos(e.pos))
            v
          } else ap
        } else id
    }
    def reorder(e: Expr): Unit = e match {
      case Assignment(ls: Apply, rs: Apply) =>
        val sym1 = ls.target.sym
        val sym2 = rs.target.sym
        if(sym1.returnArity != sym2.returnArity)
          error(s"Arity mismatch in assignment: ${sym1.returnArity} != ${sym2.returnArity}", e)
        if(sym1.returnArity == 1) {
          val v = mk().setPos(e.pos)
          buf += Assignment(v, ls).setPos(ls.pos)
          buf += Assignment(v, rs).setPos(rs.pos)
        } else {
          val vs = (0 until sym1.returnArity).map(_ => mk().setPos(e.pos)).toVector
          buf += Assignment(Tuple(vs).setPos(ls.pos), ls).setPos(ls.pos)
          buf += Assignment(Tuple(vs).setPos(rs.pos), rs).setPos(rs.pos)
        }
      case Assignment(ls: Apply, rs) => reorder(Assignment(rs, ls).setPos(e.pos))
      case Assignment(Tuple(ls), Tuple(rs)) =>
        ls.zip(rs).foreach { case (l, r) => reorder(Assignment(l, r).setPos(e.pos)) }
      case e => buf += e
    }
    exprs.foreach { e =>
      val wild = mk()
      reorder(unnest(expandWildcards(e, wild), false))
      if(assigned.contains(wild)) error("Unexpected wildcard outside of assignment", e)
    }
    buf.toSeq
  }

  // reorder assignments as if every def was a cons
  def toConsOrder(e: Expr): Expr = e match {
    case Assignment(id  @ IdentOrTuple(es), a @ Apply(t, emb, args)) =>
      if(!t.sym.isDef) Assignment(id, ApplyCons(t, emb, args).setPos(a.pos)).setPos(e.pos) else Assignment(args.head, ApplyCons(t, emb, args.tail ++ es).setPos(a.pos)).setPos(e.pos)
    case Apply(t, emb, args) =>
      if(!t.sym.isDef) ApplyCons(t, emb, args).setPos(e.pos) else Assignment(args.head, ApplyCons(t, emb, args.tail).setPos(e.pos))
    case e => e
  }

  // convert from cons-order ANF back to inlined expressions
  def toInline(es: Seq[Expr]): Seq[Expr] = {
    if(es.isEmpty) es
    else {
      val vars = mutable.HashMap.from(es.init.map { case a: Assignment => (a.lhs, a) })
      def f(e: Expr): Expr = e match {
        case e: Ident => vars.remove(e).map { a => f(a.rhs) }.getOrElse(e)
        case e: Tuple => vars.remove(e).map { a => f(a.rhs) }.getOrElse(e)
        case ApplyCons(target, emb, args) => ApplyCons(target, emb, args.map(f)).setPos(e.pos)
        case Assignment(l, r) => Assignment(f(r), f(l)).setPos(e.pos)
      }
      val e2 = f(es.last)
      (vars.valuesIterator ++ Iterator.single(e2)).toSeq
    }
  }
}
