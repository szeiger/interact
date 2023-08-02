package de.szeiger.interact

import de.szeiger.interact.ast._

class Prepare(global: Global) {
  import global._

  def apply(unit: CompilationUnit): Unit = {
    // Enter constructor symbols and collect different statement types
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
    checkThrow()
  }

  // Assign symbols everywhere and check function calls and linearity
  private def assign(n: Node, scope: Symbols, embedded: Boolean): Unit = n match {
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
    case Cons(_, args, _, _, embId, ret, der) =>
      val sc = globalSymbols.sub()
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
      val sc = globalSymbols.sub()
      defs.foreach(assign(_, sc, false))
      embDefs.foreach(assign(_, sc, true))
      val refs = new RefsMap
      defs.foreach(refs.collect)
      if(refs.hasError) error(s"Non-linear use of variable(s) ${refs.err.map(s => s"'$s'").mkString(", ")}", n)
    case n => n.nodeChildren.foreach(assign(_, scope, embedded))
  }
}
