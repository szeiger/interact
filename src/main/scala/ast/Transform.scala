package de.szeiger.interact.ast

import de.szeiger.interact.{BranchWiring, Connection, CreateLabelsComp, EmbArg, InitialRuleWiring, PayloadAssignment, PayloadComputation, PayloadMethodApplication, PayloadMethodApplicationWithReturn, RuleWiring}

abstract class Transform {
  import Transform._

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
    else n.copy(on2, red2)
  }

  def apply(n: IdentOrWildcard): IdentOrWildcard = n match {
    case n: Ident => apply(n)
    case n: Wildcard => apply(n)
  }

  def apply(n: Apply): Apply = {
    val t2 = apply(n.target)
    val emb2 = mapOC(n.embedded)(apply)
    val args2 = mapC(n.args)(apply)
    if((t2 eq n.target) && (emb2 eq n.embedded) && (args2 eq n.args)) n
    else n.copy(t2, emb2, args2)
  }

  def apply(n: ApplyCons): ApplyCons = {
    val t2 = apply(n.target)
    val emb2 = mapOC(n.embedded)(apply)
    val args2 = mapC(n.args)(apply)
    if((t2 eq n.target) && (emb2 eq n.embedded) && (args2 eq n.args)) n
    else n.copy(t2, emb2, args2)
  }

  def apply(n: Tuple): Tuple = {
    val e2 = mapC(n.exprs)(apply)
    if(e2 eq n.exprs) n
    else n.copy(e2)
  }

  def apply(n: Assignment): Assignment = {
    val l2 = apply(n.lhs)
    val r2 = apply(n.rhs)
    if((l2 eq n.lhs) && (r2 eq n.rhs)) n
    else n.copy(l2, r2)
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
    else n.copy(m2, args2, n.op, n.embTp)
  }

  def apply(n: EmbeddedAssignment): EmbeddedAssignment = {
    val l2 = apply(n.lhs)
    val r2 = apply(n.rhs)
    if((l2 eq n.lhs) && (r2 eq n.rhs)) n
    else n.copy(l2, r2)
  }

  def apply(n: CreateLabels): CreateLabels = n

  def apply(n: EmbeddedExpr): EmbeddedExpr = n match {
    case n: StringLit => apply(n)
    case n: IntLit => apply(n)
    case n: Ident => apply(n)
    case n: EmbeddedApply => apply(n)
    case n: EmbeddedAssignment => apply(n)
    case n: CreateLabels => apply(n)
  }

  def apply(n: Match): Vector[Statement] = Vector({
    val on2 = mapC(n.on)(apply)
    val red2 = mapC(n.reduced)(apply)
    if((on2 eq n.on) && (red2 eq n.reduced)) n
    else n.copy(on2, red2)
  })

  def apply(n: Cons): Vector[Statement] = Vector({
    val n2 = apply(n.name)
    val a2 = mapC(n.args)(apply)
    val e2 = mapOC(n.embeddedId)(apply)
    val r2 = mapOC(n.ret)(apply)
    val d2 = mapOC(n.der)(mapC(_)(apply))
    if((n2 eq n.name) && (a2 eq n.args) && (e2 eq n.embeddedId) && (r2 eq n.ret) && (d2 eq n.der)) n
    else n.copy(n2, a2, n.operator, n.payloadType, e2, r2, d2)
  })

  def apply(n: Let): Vector[Statement] = Vector({
    val d2 = mapC(n.defs)(apply)
    val e2 = mapC(n.embDefs)(apply)
    val f2 = mapC(n.free)(apply)
    if((d2 eq n.defs) && (e2 eq n.embDefs) && (f2 eq n.free)) n
    else n.copy(d2, e2, f2)
  })

  def apply(n: Def): Vector[Statement] = Vector({
    val n2 = apply(n.name)
    val a2 = mapC(n.args)(apply)
    val e2 = mapOC(n.embeddedId)(apply)
    val r2 = mapC(n.ret)(apply)
    val u2 = mapC(n.rules)(apply)
    if((n2 eq n.name) && (a2 eq n.args) && (e2 eq n.embeddedId) && (r2 eq n.ret) && (u2 eq n.rules)) n
    else n.copy(n2, a2, n.operator, n.payloadType, e2, r2, u2)
  })

  def apply(n: Statement): Vector[Statement] = n match {
    case n: Match => apply(n)
    case n: Cons => apply(n)
    case n: Let => apply(n)
    case n: Def => apply(n)
    case n: CheckedRule => apply(n)
    case n: RuleWiring => apply(n)
    case n: InitialRuleWiring => apply(n)
  }

  def apply(n: CheckedRule): Vector[Statement] = n match {
    case n: DerivedRule => apply(n)
    case n: MatchRule => apply(n)
  }

  def apply(n: DerivedRule): Vector[Statement] = Vector(n)

  def apply(n: MatchRule): Vector[Statement] = Vector({
    val i1 = apply(n.id1)
    val i2 = apply(n.id2)
    val a12 = mapC(n.args1)(apply)
    val a22 = mapC(n.args2)(apply)
    val emb12 = mapOC(n.emb1)(apply)
    val emb22 = mapOC(n.emb2)(apply)
    val red2 = mapC(n.branches)(apply)
    if((i1 eq n.id1) && (i2 eq n.id2) && (a12 eq n.args1) && (a22 eq n.args2) && (emb12 eq n.emb1) && (emb22 eq n.emb2) && (red2 eq n.branches)) n
    else n.copy(i1, i2, a12, a22, emb12, emb22, red2)
  })

  def apply(n: RuleWiring): Vector[Statement] = Vector({
    val b2 = mapC(n.branches)(apply)
    if(b2 eq n.branches) n
    else n.copy(n.sym1, n.sym2, b2, n.derived)
  })

  def apply(n: InitialRuleWiring): Vector[Statement] = Vector({
    val b2 = apply(n.branch)
    if(b2 eq n.branch) n
    else n.copy(branch = b2)
  })

  def apply(n: BranchWiring): BranchWiring = {
    val co2 = flatMapC(n.conns)(apply)
    val pc2 = flatMapOC(n.payloadComps)(apply)
    val cn2 = flatMapOC(n.cond)(apply)
    val bw2 = mapC(n.branches)(apply)
    if((co2 eq n.conns) && (pc2 eq n.payloadComps) && (cn2 eq n.cond) && (bw2 eq n.branches)) n
    else n.copy(n.cells, co2, pc2, cn2, bw2)
  }

  def apply(n: Connection): Set[Connection] = Set(n)

  def apply(n: CompilationUnit): CompilationUnit = {
    val st2 = flatMapC(n.statements)(apply)
    if(st2 eq n.statements) n
    else n.copy(st2)
  }

  def apply(n: Branch): Branch = {
    val cond2 = mapOC(n.cond)(apply)
    val embRed2 = mapC(n.embRed)(apply)
    val red2 = mapC(n.reduced)(apply)
    if((cond2 eq n.cond) && (embRed2 eq n.embRed) && (red2 eq n.reduced)) n
    else n.copy(cond2, embRed2, red2)
  }

  def apply(n: EmbArg): EmbArg = n

  def apply(n: PayloadComputation): Option[PayloadComputation] = Some(n match {
    case n: PayloadMethodApplication => apply(n)
    case n: PayloadMethodApplicationWithReturn => apply(n)
    case n: PayloadAssignment => apply(n)
    case n: CreateLabelsComp => apply(n)
  })

  def apply(n: PayloadMethodApplication): PayloadMethodApplication = {
    val ea2 = mapC(n.embArgs)(apply)
    if (ea2 eq n.embArgs) n
    else n.copy(embArgs = ea2)
  }

  def apply(n: PayloadMethodApplicationWithReturn): PayloadComputation = {
    val m2 = apply(n.method)
    val ri2 = apply(n.retIndex)
    if((m2 eq n.method) && (ri2 eq n.retIndex)) n
    else n.copy(method = m2, retIndex = ri2)
  }

  def apply(n: PayloadAssignment): PayloadComputation = {
    val si2 = apply(n.sourceIdx)
    val ti2 = apply(n.targetIdx)
    if((si2 eq n.sourceIdx) && (ti2 eq n.targetIdx)) n
    else n.copy(sourceIdx = si2, targetIdx = ti2)
  }

  def apply(n: CreateLabelsComp): PayloadComputation = {
    val ea2 = mapC(n.embArgs)(apply)
    if (ea2 eq n.embArgs) n
    else n.copy(embArgs = ea2)
  }
}

object Transform {
  def mapC[T,R](xs: Vector[T])(f: T => R): Vector[R] = {
    var changed = false
    val xs2 = xs.map { x =>
      val x2 = f(x)
      if(x2.asInstanceOf[AnyRef] ne x.asInstanceOf[AnyRef]) changed = true
      x2
    }
    if(changed) xs2 else xs.asInstanceOf[Vector[R]]
  }

  def flatMapC[T,R](xs: Vector[T])(f: T => Vector[R]): Vector[R] = {
    var changed = false
    val xs2 = xs.flatMap { x =>
      val x2 = f(x)
      if(x2.asInstanceOf[AnyRef] ne x.asInstanceOf[AnyRef]) changed = true
      x2
    }
    if(changed) xs2 else xs.asInstanceOf[Vector[R]]
  }

  def flatMapC[T,R](xs: Set[T])(f: T => Set[R]): Set[R] = {
    var changed = false
    val xs2 = xs.flatMap { x =>
      val x2 = f(x)
      if(x2.asInstanceOf[AnyRef] ne x.asInstanceOf[AnyRef]) changed = true
      x2
    }
    if(changed) xs2 else xs.asInstanceOf[Set[R]]
  }

  def flatMapOC[T,R](xs: Vector[T])(f: T => Option[R]): Vector[R] = {
    var changed = false
    val xs2 = xs.flatMap { x =>
      val x2 = f(x)
      if(x2.asInstanceOf[AnyRef] ne x.asInstanceOf[AnyRef]) changed = true
      x2
    }
    if(changed) xs2 else xs.asInstanceOf[Vector[R]]
  }

  def mapOC[T,R](o: Option[T])(f: T => R): Option[R] = o match {
    case None => o.asInstanceOf[Option[R]]
    case Some(x) =>
      val x2 = f(x)
      if(x2.asInstanceOf[AnyRef] ne x.asInstanceOf[AnyRef]) Some(x2)
      else o.asInstanceOf[Option[R]]
  }

  def flatMapOC[T,R](o: Option[T])(f: T => Option[R]): Option[R] = o match {
    case None => o.asInstanceOf[Option[R]]
    case Some(x) =>
      f(x) match {
        case s @ Some(x2) if x.asInstanceOf[AnyRef] ne x2.asInstanceOf[AnyRef] => s
        case _ => o.asInstanceOf[Option[R]]
      }
  }
}
