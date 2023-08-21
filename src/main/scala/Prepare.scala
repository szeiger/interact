package de.szeiger.interact

import de.szeiger.interact.ast._

/**
 * Create all symbols and check function calls and linearity.
 */
class Prepare(global: Global) extends Phase {
  import global._

  def apply(unit: CompilationUnit): CompilationUnit = {
    unit.statements.foreach {
      case c: Cons =>
        if(globalSymbols.contains(c.name)) error(s"Duplicate cons/def: ${c.name.s}", c.name)
        else c.name.sym = globalSymbols.defineCons(c.name.s, c.args.length, c.payloadType)
      case d: Def =>
        if(globalSymbols.contains(d.name)) error(s"Duplicate cons/def: ${d.name.s}", d.name)
        else d.name.sym = globalSymbols.defineDef(d.name.s, d.args.length, d.ret.length, d.payloadType)
      case _ =>
    }
    assign(unit, globalSymbols)
    unit
  }

  private[this] def assign(n: CompilationUnit, scope: Symbols): Unit =
    n.statements.foreach(assign(_, scope))

  private[this] def assign(n: Statement, scope: Symbols): Unit = n match {
    case Cons(_, args, _, _, embId, ret, der) =>
      val sc = scope.sub()
      args.foreach(assign(_, sc))
      args.foreach(a => if(a.isWildcard) error("No wildcard parameters allowed in cons", a))
      ret.foreach(assign(_: Expr, sc))
      embId.foreach(assign(_: EmbeddedExpr, sc))
      der.foreach(_.foreach { i =>
        val symO = scope.get(i)
        if(!symO.exists(_.isCons))
          error(s"No constructor '${i.s}' defined", i)
        else i.sym = symO.get
      })
    case Def(_, args, _, _, embId, ret, rules) =>
      val sc = scope.sub()
      args.foreach(assign(_, sc))
      ret.foreach(assign(_, sc))
      embId.foreach(assign(_: EmbeddedExpr, sc))
      val rm = new RefsMap
      args.foreach(rm.collect)
      ret.foreach(rm.collect)
      embId.foreach(rm.collect)
      if(rm.hasNonFree)
        error(s"Duplicate variable(s) in def pattern ${rm.nonFree.map(s => s"'$s'").mkString(", ")}", n)
      rules.foreach(assign(_, sc, rm))
    case Match(on, reduced) =>
      val sc = scope.sub()
      on.foreach(assign(_, sc))
      val rm = new RefsMap
      on.foreach(rm.collect)
      if(rm.hasNonFree)
        error(s"Duplicate variable(s) in match pattern ${rm.nonFree.map(s => s"'$s'").mkString(", ")}", n)
      reduced.foreach(assign(_, sc))
    case Let(defs, embDefs) =>
      val sc = scope.sub()
      defs.foreach(assign(_, sc))
      embDefs.foreach(assign(_, sc))
      val refs = new RefsMap
      defs.foreach(refs.collect)
      if(refs.hasError)
        error(s"Non-linear use of variable(s) ${refs.err.map(s => s"'$s'").mkString(", ")}", n)
    case _: CheckedRule =>
  }

  private[this] def assign(n: DefRule, scope: Symbols, defRefs: RefsMap): Unit = {
    val sc = scope.sub()
    n.on.foreach(assign(_, sc))
    val rm = defRefs.sub()
    n.on.foreach(rm.collect)
    if(rm.hasNonFree)
      error(s"Duplicate variable(s) in def rule pattern ${rm.nonFree.map(s => s"'$s'").mkString(", ")}", n)
    n.reduced.foreach(assign(_, sc))
  }

  private[this] def assign(n: Branch, scope: Symbols): Unit = {
    val sc = scope.sub()
    n.cond.foreach(assign(_, sc))
    n.reduced.foreach(assign(_, sc))
    n.embRed.foreach(assign(_, sc))
  }

  private[this] def define(n: Ident, scope: Symbols, embedded: Boolean): Symbol = {
    scope.get(n) match {
      case Some(s) =>
        if(s.isEmbedded && !embedded)
          error(s"Embedded variable '$s' used in non-embedded context", n)
        else if(!s.isEmbedded && embedded)
          error(s"Non-embedded variable '$s' used in embedded context", n)
        s
      case None =>
        scope.define(n.s, isEmbedded = embedded)
    }
  }

  private[this] def assign(n: Expr, scope: Symbols): Unit = n match {
    case n: Ident =>
      assert(n.sym.isEmpty)
      n.sym = define(n, scope, false)
    case n: NatLit =>
      n.sSym = define(Ident("S"), scope, false)
      n.zSym = define(Ident("Z"), scope, false)
      if(!n.sSym.isCons || n.sSym.arity != 1 || !n.zSym.isCons || n.zSym.arity != 0)
        error(s"Nat literal requires appropriate Z() and S(_) constructors", n)
    case Apply(id, emb, args) =>
      assign(id: Expr, scope)
      emb.foreach(assign(_: EmbeddedExpr, scope))
      val l = args.length
      if(!id.sym.isCons)
        error(s"Symbol '${id.sym}' in function call is not a constructor", id)
      else if(id.sym.callArity != l)
        error(s"Wrong number of arguments for '${id.sym}': got $l, expected ${id.sym.callArity}", n)
      if(l == 1) assign(args.head, scope) // tail-recursive call
      else if(l > 0) args.foreach(assign(_, scope))
    case n => n.nodeChildren.foreach {
      case ch: Expr => assign(ch, scope)
    }
  }

  private[this] def assign(n: EmbeddedExpr, scope: Symbols): Unit = n match {
    case n: Ident =>
      assert(n.sym.isEmpty)
      n.sym = define(n, scope, true)
    case EmbeddedApply(_, args, _) =>
      args.foreach(assign(_, scope))
    case n => n.nodeChildren.foreach {
      case ch: EmbeddedExpr => assign(ch, scope)
    }
  }
}
