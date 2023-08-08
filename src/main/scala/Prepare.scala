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
    assign(unit, globalSymbols, false)
    unit
  }

  private[this] def assign(n: Node, scope: Symbols, embedded: Boolean): Unit = n match {
    case n: Ident =>
      assert(n.sym.isEmpty)
      scope.get(n) match {
        case Some(s) =>
          if(s.isEmbedded && !embedded)
            error(s"Embedded variable '$s' used in non-embedded context", n)
          else if(!s.isEmbedded && embedded)
            error(s"Non-embedded variable '$s' used in embedded context", n)
          n.sym = s
        case None =>
          n.sym = scope.define(n.s, isEmbedded = embedded)
      }
    case n: NatLit =>
      val sId = Ident("S")
      val zId = Ident("Z")
      assign(sId, scope, embedded)
      assign(zId, scope, embedded)
      n.sSym = sId.sym
      n.zSym = zId.sym
    case Cons(_, args, _, _, embId, ret, der) =>
      val sc = scope.sub()
      args.foreach(assign(_, sc, false))
      args.foreach(a => if(a.isWildcard) error(s"No wildcard parameters allowed in cons", a))
      ret.foreach(assign(_, sc, false))
      embId.foreach(assign(_, sc, true))
      der.foreach(_.foreach { i =>
        val symO = scope.get(i)
        if(!symO.exists(_.isCons))
          error(s"No constructor '${i.s}' defined", i)
        else i.sym = symO.get
      })
    case Def(_, args, _, _, embId, ret, rules) =>
      val sc = scope.sub()
      args.foreach(assign(_, sc, false))
      ret.foreach(assign(_, sc, false))
      embId.foreach(assign(_, sc, true))
      rules.foreach(assign(_, sc, false))
    case DefRule(on, reduced) =>
      val sc = scope.sub()
      on.foreach(assign(_, sc, false))
      reduced.foreach(assign(_, sc, false))
    case Match(on, reduced) =>
      val sc = scope.sub()
      on.foreach(assign(_, sc, false))
      reduced.foreach(assign(_, sc, false))
    case Branch(cond, embRed, red) =>
      val sc = scope.sub()
      cond.foreach(assign(_, sc, true))
      embRed.foreach(assign(_, sc, true))
      red.foreach(assign(_, sc, false))
    case n @ Apply(id, emb, args) =>
      assign(id, scope, embedded)
      emb.foreach(assign(_, scope, true))
      val l = args.length
      if(!id.sym.isCons)
        error(s"Symbol '${id.sym}' in function call is not a constructor", id)
      else if(id.sym.callArity != l)
        error(s"Wrong number of arguments for '${id.sym}': got $l, expected ${id.sym.callArity}", n)
      if(l == 1) assign(args.head, scope, embedded) // tail-recursive call for numerals
      else if(l > 0) args.foreach(assign(_, scope, embedded))
    case EmbeddedApply(_, args) =>
      args.foreach(assign(_, scope, true))
    case n @ Let(defs, embDefs) =>
      val sc = scope.sub()
      defs.foreach(assign(_, sc, false))
      embDefs.foreach(assign(_, sc, true))
      val refs = new RefsMap
      defs.foreach(refs.collect)
      if(refs.hasError) error(s"Non-linear use of variable(s) ${refs.err.map(s => s"'$s'").mkString(", ")}", n)
    case n => n.nodeChildren.foreach(assign(_, scope, embedded))
  }
}
