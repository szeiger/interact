package de.szeiger.interact.ast

abstract class Transform {
  def apply(n: Node): Node = n match {
    case n: Branch => apply(n)
    case n: DefRule => apply(n)
    case n: Expr => apply(n)
    case n: EmbeddedExpr => apply(n)
    case n: Statement =>
      val v = apply(n: Statement)
      assert(v.length == 1)
      v.head
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
    case n: NatLit => apply(n)
  }

  def apply(n: NatLit): NatLit = n

  def apply(n: StringLit): StringLit = n

  def apply(n: IntLit): IntLit = n

  def apply(n: Ident): Ident = n

  def apply(n: Wildcard): Wildcard = n

  def apply(n: EmbeddedApply): EmbeddedApply = {
    val m2 = mapC(n.methodQNIds)(apply)
    val args2 = mapC(n.args)(apply)
    if((m2 eq n.methodQNIds) && (args2 eq n.args)) n
    else EmbeddedApply(m2, args2, n.op, n.embTp).setPos(n.pos)
  }

  def apply(n: EmbeddedAssignment): EmbeddedAssignment = {
    val l2 = apply(n.lhs)
    val r2 = apply(n.rhs)
    if((l2 eq n.lhs) && (r2 eq n.rhs)) n
    else EmbeddedAssignment(l2, r2).setPos(n.pos)
  }

  def apply(n: EmbeddedExpr): EmbeddedExpr = n match {
    case n: StringLit => apply(n)
    case n: IntLit => apply(n)
    case n: Ident => apply(n)
    case n: EmbeddedApply => apply(n)
    case n: EmbeddedAssignment => apply(n)
  }

  def apply(n: Match): Vector[Statement] = Vector({
    val on2 = mapC(n.on)(apply)
    val red2 = mapC(n.reduced)(apply)
    if((on2 eq n.on) && (red2 eq n.reduced)) n
    else Match(on2, red2).setPos(n.pos)
  })

  def apply(n: Cons): Vector[Statement] = Vector({
    val n2 = apply(n.name)
    val a2 = mapC(n.args)(apply)
    val e2 = mapC(n.embeddedId)(apply)
    val r2 = mapC(n.ret)(apply)
    val d2 = mapC(n.der)(mapC(_)(apply))
    if((n2 eq n.name) && (a2 eq n.args) && (e2 eq n.embeddedId) && (r2 eq n.ret) && (d2 eq n.der)) n
    else Cons(n2, a2, n.operator, n.payloadType, e2, r2, d2).setPos(n.pos)
  })

  def apply(n: Let): Vector[Statement] = Vector({
    val d2 = mapC(n.defs)(apply)
    val e2 = mapC(n.embDefs)(apply)
    if((d2 eq n.defs) && (e2 eq n.embDefs)) n
    else Let(d2, e2).setPos(n.pos)
  })

  def apply(n: Def): Vector[Statement] = Vector({
    val n2 = apply(n.name)
    val a2 = mapC(n.args)(apply)
    val e2 = mapC(n.embeddedId)(apply)
    val r2 = mapC(n.ret)(apply)
    val u2 = mapC(n.rules)(apply)
    if((n2 eq n.name) && (a2 eq n.args) && (e2 eq n.embeddedId) && (r2 eq n.ret) && (u2 eq n.rules)) n
    else Def(n2, a2, n.operator, n.payloadType, e2, r2, u2).setPos(n.pos)
  })

  def apply(n: Statement): Vector[Statement] = n match {
    case n: Match => apply(n)
    case n: Cons => apply(n)
    case n: Let => apply(n)
    case n: Def => apply(n)
    case n: CheckedRule => apply(n)
  }

  def apply(n: CheckedRule): Vector[Statement] = n match {
    case n: DerivedRule => apply(n)
    case n: MatchRule => apply(n)
  }

  def apply(n: DerivedRule): Vector[Statement] = Vector(n)

  def apply(n: MatchRule): Vector[Statement] = Vector({
    val i1 = apply(n.id1)
    val i2 = apply(n.id1)
    val a12 = mapC(n.args1)(apply)
    val a22 = mapC(n.args2)(apply)
    val emb12 = mapC(n.emb1)(apply)
    val emb22 = mapC(n.emb2)(apply)
    val red2 = mapC(n.reduction)(apply)
    if((i1 eq n.id1) && (i2 eq n.id2) && (a12 eq n.args1) && (a22 eq n.args2) && (emb12 eq n.emb1) && (emb22 eq n.emb2) && (red2 eq n.reduction)) n
    else MatchRule(i1, i2, a12, a22, emb12, emb22, red2).setPos(n.pos)
  })

  def apply(n: CompilationUnit): CompilationUnit = {
    val st2 = flatMapC(n.statements)(apply)
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

  protected[this] final def flatMapC[T,R](xs: Vector[T])(f: T => Vector[R]): Vector[R] = {
    var changed = false
    val xs2 = xs.flatMap { x =>
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
