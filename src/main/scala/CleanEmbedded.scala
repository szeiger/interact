package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
 * Check usage of variables and assign payload types to embedded variables. After this phase:
 * - All Apply/ApplyCons constructor calls that need an embedded value contain an Ident
 *   which either refers to an Ident in the pattern or is computed by an EmbeddedExpr.
 * - Implicit creation and copying of labels is made explicit.
 * - PayloadTypes are assigned to all embedded Symbols.
 * - Embedded variable usage is linear.
 */
class CleanEmbedded(global: Global) extends Transform with Phase {
  import global._

  override def apply(n: Statement): Vector[Statement] = n match {
    case n: MatchRule => apply(n)
    case n: Let => apply(n)
    case n => Vector(n)
  }

  override def apply(mr: MatchRule): Vector[Statement] = {
    val rm = new RefsMap
    mr.args1.foreach(rm.collect)
    mr.args2.foreach(rm.collect)
    mr.emb1.foreach(rm.collect)
    mr.emb2.foreach(rm.collect)
    val (emb1Sym, emb1Id) = patternEmbSym(mr.id1, mr.emb1)
    val (emb2Sym, emb2Id) = patternEmbSym(mr.id2, mr.emb2)
    val patSyms = rm.allSymbols.toSet
    val branches = mr.reduction.map { b =>
      val refs = rm.sub()
      refs.collect(b)
      if(refs.hasError) {
        val nonEmbErrs = refs.err.filter(!_.isEmbedded)
        if(nonEmbErrs.nonEmpty)
          error(s"Non-linear use of variable(s) ${nonEmbErrs.map(s => s"'$s'").mkString(", ")}", b)
      }
      b.cond.foreach { cond =>
        val condSyms = new RefsMap
        condSyms.collect(cond)
        val newSyms = condSyms.allSymbols.filter(s => !patSyms.contains(s)).toSet
        if(newSyms.nonEmpty)
          error(s"Variable(s)s ${newSyms.map(s => s"'$s'").mkString(", ")} in condition do not refer to pattern", cond)
      }
      val patPayloads = mutable.HashMap.empty[Symbol, Position]
      if(emb1Sym.isDefined) patPayloads.put(emb1Sym, emb1Id.get.pos)
      if(emb2Sym.isDefined) patPayloads.put(emb2Sym, emb2Id.get.pos)
      val (es, ees) = transformReduction(b.reduced, b.embRed, patPayloads)
      b.copy(reduced = es, embRed = ees).setPos(b.pos)
    }
    //Vector(mr)
    Vector(mr.copy(reduction = branches).setPos(mr.pos))
  }

  override def apply(l: Let): Vector[Statement] = {
    val (es, ees) = transformReduction(l.defs, l.embDefs, mutable.HashMap.empty)
    Vector(l.copy(defs = es, embDefs = ees).setPos(l.pos))
  }

  private[this] def inferMethod(e: EmbeddedApply): EmbeddedType = {
    val (cln, mn) =
      if(e.op) CleanEmbedded.operators(e.methodQN.head) else (e.className, e.methodName)
    val c = dependencyLoader.loadClass(cln)
    def toPT(cl: Class[_]) = cl.getName match {
      case "void" => (PayloadType.VOID, false)
      case "int" => (PayloadType.INT, false)
      case s if s == classOf[IntBox].getName => (PayloadType.INT, true)
      case s if s == classOf[RefBox].getName => (PayloadType.REF, true)
      case _ => (PayloadType.REF, false)
    }
    c.getMethods.find(_.getName == mn) match {
      case None =>
        error(s"Method $mn not found in $cln", e)
        EmbeddedType.Unknown
      case Some(meth) =>
        val ret = toPT(meth.getReturnType)._1
        val args = meth.getParameterTypes.iterator.map(toPT).toVector
        EmbeddedType.Method(ret, args)
    }
  }

  private[this] def transformReduction(es: Vector[Expr], ees: Vector[EmbeddedExpr],
    patPayloads: mutable.HashMap[Symbol, Position]): (Vector[Expr], Vector[EmbeddedExpr]) = {
    val local = new SymbolGen("$e$", isEmbedded = true)
    val consumed = mutable.HashMap.empty[Symbol, Position]
    val extraComps = ArrayBuffer.empty[EmbeddedExpr]
    val implicitLabel = local(payloadType = PayloadType.LABEL)
    val aliasedLabels = mutable.HashMap.empty[Symbol, ArrayBuffer[Symbol]]
    def aliasLabel(es: Symbol, pos: Position): Ident = {
      val l = aliasedLabels.getOrElseUpdate(es, new ArrayBuffer[Symbol])
      val id = local.id(payloadType = PayloadType.LABEL).setPos(pos)
      l += id.sym
      id
    }
    val tr = new Transform {
      override def apply(n: Expr): Expr = n match {
        case n @ AnyApply(target, embedded, args, _) =>
          embedded match {
            case Some(ei: Ident) =>
              val pt = target.sym.payloadType
              // Check matching PayloadType is the symbol is not new
              if(ei.sym.payloadType.isDefined) {
                if(ei.sym.payloadType != pt) error(s"Inconsistent type for embedded variable: $pt != ${ei.sym.payloadType}", target)
              } else {
                assert(ei.sym.payloadType.isEmpty)
                ei.sym.payloadType = pt
              }
              // Replace new (non-pattern) label with an alias to allow copying
              if(pt == PayloadType.LABEL && !patPayloads.contains(ei.sym))
                n.copy(target, Some(aliasLabel(ei.sym, ei.pos)), args.map(apply)).setPos(n.pos)
              else {
                val old = consumed.put(ei.sym, ei.pos)
                if(old.isDefined && !pt.canCopy) error(s"Cannot copy embedded value of type $pt", ei.pos)
                super.apply(n)
              }
            case Some(ee) =>
              val id = local.id(payloadType = target.sym.payloadType).setPos(ee.pos)
              consumed.put(id.sym, id.pos)
              extraComps += EmbeddedAssignment(id, ee).setPos(ee.pos)
              n.copy(target, Some(id), args.map(apply)).setPos(n.pos)
            case None if target.sym.payloadType.isDefined =>
              if(target.sym.payloadType == PayloadType.LABEL)
                n.copy(target, Some(aliasLabel(implicitLabel, target.pos)), args.map(apply)).setPos(n.pos)
              else {
                error(s"Embedded value of type ${target.sym.payloadType} must be specified", target)
                super.apply(n)
              }
            case None => super.apply(n)
          }
        case n => super.apply(n)
      }
      override def apply(n: EmbeddedExpr): EmbeddedExpr = n // skip
    }
    val es2 = es.map(tr(_))
    aliasedLabels.foreach { case (base, syms) =>
      extraComps += CreateLabels(base, syms.toVector)
    }
    val embComps = (extraComps.iterator ++ ees.iterator).toVector

    println(s"**** implicitLabel = $implicitLabel")
    println(s"     aliasedLabels = $aliasedLabels")
    println(s"          consumed = ${consumed.mkString(", ")}")
    extraComps.foreach { e =>
      println(s"        extraComps = ${e.show}")
    }

    patPayloads.foreach { case (sym, pos) =>
      if(!consumed.contains(sym) && !sym.payloadType.canErase)
        error(s"Cannot erase embedded value of type ${sym.payloadType}", pos)
    }


//    payloads.foreach { case (s, pos) =>
//      val r = refs(s)
//      val pt = s.payloadType
//      if(!pt.canCopy && r > 2)
//        error(s"Cannot copy embedded value of type $pt", pos)
//      else if(!pt.canCreate && !patPayloads.keySet.contains(s) && !createdSyms.contains(s))
//        error(s"Cannot create embedded value of type $pt", pos)
//      else if(!pt.canErase && r < 2)
//        error(s"Cannot erase embedded value of type $pt", pos)
//    }

    (es2, embComps)
  }

  private[this] def patternEmbSym(consId: Ident, o: Option[EmbeddedExpr]): (Symbol, Option[Ident]) = {
    val embId = o match {
      case o @ Some(i: Ident) => o.asInstanceOf[Some[Ident]]
      case Some(e) =>
        error(s"Embedded expression in pattern match must be a variable", e)
        None
      case _ => None
    }
    val embSym = embId.map(_.sym).getOrElse(Symbol.NoSymbol)
    val consPT = consId.sym.payloadType
    if(consPT.isDefined && embSym.isEmpty && !consPT.canErase)
      error(s"Embedded value of type $consPT must be extracted in pattern match", consId)
    else if(embSym.isDefined) {
      if(consPT.isEmpty)
        error(s"Constructor has no embedded value", consId)
      else embSym.payloadType = consPT
    }
    (embSym, embId)
  }
}

object CleanEmbedded {
  private val operators = Map(
    "==" -> (Intrinsics.getClass.getName, "eq"),
    "+" -> (Intrinsics.getClass.getName, "intAdd"),
    "-" -> (Intrinsics.getClass.getName, "intSub"),
  )
}