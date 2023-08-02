package de.szeiger.interact.ast

abstract class Transform {
  def apply(n: Node): Node = n match {
    case n: Branch => apply(n)
    case n: DefRule => apply(n)
    case n: Expr => apply(n)
    case n: EmbeddedExpr => apply(n)
    case n: Statement => apply(n)
    case n: CompilationUnit => apply(n)
  }

  def apply(n: DefRule): DefRule = {
    val on2 = mapC(n.on)(apply)
    val red2 = mapC(n.reduced)(apply)
    if((on2 eq n.on) && (red2 eq n.reduced)) n
    else DefRule(on2, red2).setPos(n.pos)
  }

  def apply(n: IdentOrWildcard): IdentOrWildcard = n match {
    case n: Ident => apply(n)
    case n: Wildcard => apply(n)
  }

  def apply(n: Apply): Apply = {
    val t2 = apply(n.target)
    val emb2 = mapC(n.embedded)(apply)
    val args2 = mapC(n.args)(apply)
    if((t2 eq n.target) && (emb2 eq n.embedded) && (args2 eq n.args)) n
    else Apply(t2, emb2, args2).setPos(n.pos)
  }

  def apply(n: ApplyCons): ApplyCons = {
    val t2 = apply(n.target)
    val emb2 = mapC(n.embedded)(apply)
    val args2 = mapC(n.args)(apply)
    if((t2 eq n.target) && (emb2 eq n.embedded) && (args2 eq n.args)) n
    else ApplyCons(t2, emb2, args2).setPos(n.pos)
  }

  def apply(n: Tuple): Tuple = {
    val e2 = mapC(n.exprs)(apply)
    if(e2 eq n.exprs) n
    else Tuple(e2).setPos(n.pos)
  }

  def apply(n: Assignment): Assignment = {
    val l2 = apply(n.lhs)
    val r2 = apply(n.rhs)
    if((l2 eq n.lhs) && (r2 eq n.rhs)) n
    else Assignment(l2, r2).setPos(n.pos)
  }

  def apply(n: Expr): Expr = n match {
    case n: IdentOrWildcard => apply(n)
    case n: Apply => apply(n)
    case n: ApplyCons => apply(n)
    case n: Tuple => apply(n)
    case n: Assignment => apply(n)
  }

  def apply(n: StringLit): StringLit = n

  def apply(n: IntLit): IntLit = n

  def apply(n: Ident): Ident = n

  def apply(n: Wildcard): Wildcard = n

  def apply(n: EmbeddedApply): EmbeddedApply = {
    val m2 = mapC(n.methodQNIds)(apply)
    val args2 = mapC(n.args)(apply)
    if((m2 eq n.methodQNIds) && (args2 eq n.args)) n
    else EmbeddedApply(m2, args2).setPos(n.pos)
  }

  def apply(n: EmbeddedExpr): EmbeddedExpr = n match {
    case n: StringLit => apply(n)
    case n: IntLit => apply(n)
    case n: Ident => apply(n)
    case n: EmbeddedApply => apply(n)
  }

  def apply(n: Match): Match = {
    val on2 = apply(n.on)
    val red2 = mapC(n.reduced)(apply)
    if((on2 eq n.on) && (red2 eq n.reduced)) n
    else Match(on2, red2).setPos(n.pos)
  }

  def apply(n: Cons): Cons = {
    val n2 = apply(n.name)
    val a2 = mapC(n.args)(apply)
    val e2 = mapC(n.embeddedId)(apply)
    val r2 = mapC(n.ret)(apply)
    val d2 = mapC(n.der)(mapC(_)(apply))
    if((n2 eq n.name) && (a2 eq n.args) && (e2 eq n.embeddedId) && (r2 eq n.ret) && (d2 eq n.der)) n
    else Cons(n2, a2, n.operator, n.payloadType, e2, r2, d2).setPos(n.pos)
  }

  def apply(n: Let): Let = {
    val d2 = mapC(n.defs)(apply)
    val e2 = mapC(n.embDefs)(apply)
    if((d2 eq n.defs) && (e2 eq n.embDefs)) n
    else Let(d2, e2).setPos(n.pos)
  }

  def apply(n: Def): Def = {
    val n2 = apply(n.name)
    val a2 = mapC(n.args)(apply)
    val e2 = mapC(n.embeddedId)(apply)
    val r2 = mapC(n.ret)(apply)
    val u2 = mapC(n.rules)(apply)
    if((n2 eq n.name) && (a2 eq n.args) && (e2 eq n.embeddedId) && (r2 eq n.ret) && (u2 eq n.rules)) n
    else Def(n2, a2, n.operator, n.payloadType, e2, r2, u2).setPos(n.pos)
  }

  def apply(n: Statement): Statement = n match {
    case n: Match => apply(n)
    case n: Cons => apply(n)
    case n: Let => apply(n)
    case n: Def => apply(n)
  }

  def apply(n: CompilationUnit): CompilationUnit = {
    val st2 = mapC(n.statements)(apply)
    if(st2 eq n.statements) n
    else CompilationUnit(st2).setPos(n.pos)
  }

  def apply(n: Branch): Branch = {
    val cond2 = mapC(n.cond)(apply)
    val embRed2 = mapC(n.embRed)(apply)
    val red2 = mapC(n.reduced)(apply)
    if((cond2 eq n.cond) && (embRed2 eq n.embRed) && (red2 eq n.reduced)) n
    else Branch(cond2, embRed2, red2).setPos(n.pos)
  }

  protected[this] final def mapC[T,R](xs: Vector[T])(f: T => R): Vector[R] = {
    var changed = false
    val xs2 = xs.map { x =>
      val x2 = f(x)
      if(x2.asInstanceOf[AnyRef] != x.asInstanceOf[AnyRef]) changed = true
      x2
    }
    if(changed) xs2 else xs.asInstanceOf[Vector[R]]
  }

  protected[this] final def mapC[T,R](o: Option[T])(f: T => R): Option[R] = o match {
    case None => o.asInstanceOf[Option[R]]
    case Some(x) =>
      val x2 = f(x)
      if(x2.asInstanceOf[AnyRef] != x.asInstanceOf[AnyRef]) Some(x2)
      else o.asInstanceOf[Option[R]]
  }
}
