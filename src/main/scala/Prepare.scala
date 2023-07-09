package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable

class Prepare(global: Global) {
  import global._

  def apply(unit: CompilationUnit): Unit = {
    // Enter constructor symbols and collect different statement types
    unit.statements.foreach {
      case c: Cons =>
        if(globalSymbols.get(c.name.s).isDefined) error(s"Duplicate cons/def: ${c.name.s}", c.name)
        else {
          c.args.foreach(a => if(a == null) error(s"No wildcard parameters allowed in cons", a))
          c.name.sym = globalSymbols.define(c.name.s, isCons = true, arity = c.args.length, payloadType = c.payloadType)
        }
      case d: Def =>
        if(globalSymbols.get(d.name.s).isDefined) error(s"Duplicate cons/def: ${d.name.s}", d.name)
        else
          d.name.sym = globalSymbols.define(d.name.s, isCons = true, isDef = true, arity = d.args.length + d.ret.length - 1, returnArity = d.ret.length, payloadType = d.payloadType)
      case _ =>
    }
    // Assign symbols everywhere
    assign(unit, globalSymbols, false)
    // Check variable usage
    check(unit)
    checkThrow()
  }

  private def assign(n: Node, scope: Symbols, embedded: Boolean): Unit = n match {
    case n: Ident =>
      assert(n.sym.isEmpty)
      scope.get(n.s) match {
        case Some(s) =>
          if(s.isEmbedded && !embedded)
            error(s"Embedded variable '$s' used in non-embedded context", n)
          else if(!s.isEmbedded && embedded)
            error(s"Non-embedded variable '$s' used in embedded context", n)
          n.sym = s
        case None =>
          n.sym = scope.define(n.s, isEmbedded = embedded)
      }
    case Let(defs, embDefs) =>
      val sc = globalSymbols.sub()
      defs.foreach(assign(_, sc, false))
      embDefs.foreach(assign(_, sc, true))
    case Cons(_, args, _, _, embId, ret, der) =>
      val sc = globalSymbols.sub()
      args.foreach(assign(_, sc, false))
      ret.foreach(assign(_, sc, false))
      embId.foreach(assign(_, sc, true))
      der.foreach(_.foreach(assign(_, scope, false)))
    case Def(_, args, _, _, embId, ret, rules) =>
      val sc = globalSymbols.sub()
      args.foreach(assign(_, sc, false))
      ret.foreach(assign(_, sc, false))
      embId.foreach(assign(_, sc, true))
      rules.foreach(assign(_, sc, false))
    case DefRule(on, reduced) =>
      val sc = globalSymbols.sub()
      on.foreach(assign(_, sc, false))
      reduced.foreach(assign(_, sc, false))
    case Match(on, reduced) =>
      val sc = globalSymbols.sub()
      assign(on, sc, false)
      reduced.foreach(assign(_, sc, false))
    case Branch(cond, embRed, red) =>
      val sc = globalSymbols.sub()
      cond.foreach(assign(_, sc, true))
      embRed.foreach(assign(_, sc, true))
      red.foreach(assign(_, sc, false))
    case Apply(target, emb, args) =>
      assign(target, scope, embedded)
      emb.foreach(assign(_, scope, true))
      val l = args.length
      if(l == 1) assign(args.head, scope, embedded) // tail-recursive call for numerals
      else if(l > 0) args.foreach(assign(_, scope, embedded))
    case EmbeddedApply(_, args) =>
      args.foreach(assign(_, scope, true))
    case n => n.nodeChildren.foreach(assign(_, scope, embedded))
  }

  private def check(n: Node): Unit = n match {
    case CompilationUnit(ns) => ns.foreach(check)
    case n: Let => checkLet(n)
    case _ =>
  }

  private def checkLet(let: Let): Unit = {
    val refs = new RefsMap
    def f(e: Expr): Unit = e match {
      case Assignment(l, r) => f(l); f(r)
      case Tuple(es) => es.foreach(f)
      case Wildcard() =>
      case e @ Ident(s) =>
        if(e.sym.isCons) f(Apply(e, None, Nil).setPos(e.pos))
        else refs.inc(e.sym)
      case Apply(id @ Ident(s), _, args) =>
        if(!id.sym.isCons) error(s"Symbol '${id.sym}' in function call is not a constructor", id)
        else {
          val a = id.sym.callArity
          if(a != args.length) error(s"Wrong number of arguments for '$s': got ${args.length}, expected $a", id)
        }
        args.foreach(f)
      case e => error(s"Internal error: Unsupported expression in let clause", e)
    }
    let.defs.foreach(f)
    val err = refs.err.toSeq
    if(err.nonEmpty) error(s"Non-linear use of variable(s) ${err.map(s => s"'$s'").mkString(", ")}", let)
  }
}
