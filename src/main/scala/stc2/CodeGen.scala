package de.szeiger.interact.stc2

import de.szeiger.interact.codegen.{AbstractCodeGen, ClassWriter, ParSupport}
import de.szeiger.interact.{Config, IntBox, IntBoxImpl, RefBox, RefBoxImpl, RulePlan}
import de.szeiger.interact.ast.{CompilationUnit, PayloadType, RuleKey, Symbol, SymbolKind, Symbols}
import de.szeiger.interact.codegen.AbstractCodeGen.{encodeName, symbolT}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}

import scala.collection.mutable

class CodeGen(genPackage: String, classWriter: ClassWriter, val config: Config,
  compilationUnit: CompilationUnit, globals: Symbols, val symIds: Map[Symbol, Int], symBits: Int) extends AbstractCodeGen(config) {

  val riT = tp.c[InitialRuleImpl]
  val ptwT = tp.c[Interpreter]
  val cellT = tp.c[Cell]
  val metaClassT = tp.c[MetaClass]
  val dispatchT = tp.c[Dispatch]
  val intBoxT = tp.i[IntBox]
  val refBoxT = tp.i[RefBox]
  val intBoxImplT = tp.c[IntBoxImpl]
  val refBoxImplT = tp.c[RefBoxImpl]
  val generatedDispatchT = tp.c(s"$genPackage/Dispatch")
  val cellCacheT = tp.c(s"$genPackage/CellCache")
  val dispatch_reduce = dispatchT.method("reduce", tp.m(cellT, cellT, ptwT).V)
  val ri_reduce = riT.method("reduce", tp.m(cellT, cellT, ptwT).V)
  val ri_freeWires = riT.method("freeWires", tp.m()(symbolT.a))
  val metaClass_symId = metaClassT.field("symId", tp.I)
  val cell_auxCell = cellT.method("auxCell", tp.m(tp.I)(cellT))
  val cell_auxPort = cellT.method("auxPort", tp.m(tp.I).I)
  val cell_setAux = cellT.method("setAux", tp.m(tp.I, cellT, tp.I).V)
  val cell_symId = cellT.field("symId", tp.I)
  val ptw_addActive = ptwT.method("addActive", tp.m(cellT, cellT).V)
  val ptw_recordStats = ptwT.method("recordStats", tp.m(tp.I, tp.I, tp.I, tp.I, tp.I, tp.I).V)
  val ptw_recordMetric = ptwT.method("recordMetric", tp.m(tp.c[String], tp.I).V)
  val ptw_addIrreducible = ptwT.method("addIrreducible", tp.m(cellT, cellT).V)
  val intBox_getValue = intBoxT.method("getValue", tp.m().I)
  val intBox_setValue = intBoxT.method("setValue", tp.m(tp.I).V)
  val refBox_getValue = refBoxT.method("getValue", tp.m()(tp.c[AnyRef]))
  val refBox_setValue = refBoxT.method("setValue", tp.m(tp.c[AnyRef]).V)
  val new_Cell = cellT.constr(tp.m().V)
  val new_MetaClass = metaClassT.constr(tp.m(symbolT, tp.I).V)
  val new_IntBoxImpl = intBoxImplT.constr(tp.m().V)
  val new_RefBoxImpl = refBoxImplT.constr(tp.m().V)

  def ruleT_static_reduce(sym1: Symbol, sym2: Symbol) =
    tp.c(s"$genPackage/Rule_${encodeName(sym1)}$$_${encodeName(sym2)}").method("static_reduce", tp.m(concreteCellTFor(sym1), concreteCellTFor(sym2), ptwT).V)
  def initialRuleT_static_reduce(idx: Int) =
    tp.c(s"$genPackage/InitialRule_$idx").method("static_reduce", tp.m(cellT, cellT, ptwT).V)
  def concreteMetaClassTFor(sym: Symbol) = if(sym.isDefined) tp.c(s"$genPackage/M_${encodeName(sym)}") else metaClassT
  def concreteCellTFor(sk: SymbolKind): ClassOwner = tp.c(s"$genPackage/C_${sk.arity}${sk.boxType}")
  def concreteCellTFor(sym: Symbol): ClassOwner = if(sym.isDefined) concreteCellTFor(SymbolKind(sym)) else cellT
  def concreteConstrFor(sym: Symbol) =
    concreteCellTFor(sym).constr(tp.m(tp.I +: (0 until sym.arity).flatMap(_ => Seq(cellT, tp.I)): _*).V)
  def concreteReinitFor(sk: SymbolKind): MethodRef = concreteCellTFor(sk).method("reinit", tp.m((0 until sk.arity).flatMap(_ => Seq(cellT, tp.I)): _*).V)
  def concreteReinitFor(sym: Symbol): MethodRef = concreteReinitFor(SymbolKind(sym))
  def concretePayloadFieldFor(sk: SymbolKind) = concreteCellTFor(sk).field("value", sk.boxType match {
    case "I" => tp.I
    case _ => tp.c[AnyRef]
  })
  def cell_acell(sym: Symbol, p: Int) = concreteCellTFor(sym).field(s"acell$p", cellT)
  def cell_aport(sym: Symbol, p: Int) = concreteCellTFor(sym).field(s"aport$p", tp.I)
  def metaClass_singleton(sym: Symbol) = { val tp = concreteMetaClassTFor(sym); tp.field("singleton", tp) }
  def metaClass_singletonCell(sym: Symbol) = concreteMetaClassTFor(sym).field("singletonCell", concreteCellTFor(sym))
  def cellCache_var(sym: Symbol) = cellCacheT.field(s"f_${encodeName(sym)}", concreteCellTFor(sym))
  def cellCache_get(sym: Symbol) = cellCacheT.method(s"get_${encodeName(sym)}", tp.m()(concreteCellTFor(sym)))
  def cellCache_set(sym: Symbol) = cellCacheT.method(s"set_${encodeName(sym)}", tp.m(concreteCellTFor(sym)).V)

  val rules = compilationUnit.statements.collect { case g: RulePlan if !g.initial => (g.key, g) }.toMap

  private def implementStaticReduce(classDSL: ClassDSL, rule: RulePlan, mref: MethodRef): Unit = {
    val m = classDSL.method(Acc.PUBLIC.STATIC, mref.name, mref.desc)
    val needsCachedPayloads = rule.branches.iterator.flatMap(_.needsCachedPayloads).toSet
    val active = Vector(
      new ActiveCell(0, m.param("active0", concreteCellTFor(rule.sym1)), rule.sym1, rule.arity1, needsCachedPayloads.contains(0)),
      new ActiveCell(1, m.param("active1", concreteCellTFor(rule.sym2)), rule.sym2, rule.arity2, needsCachedPayloads.contains(1)),
    )
    val ptw = m.param("ptw", ptwT)
    val metricName = s"${classDSL.name}.${m.name}"
    incMetric(metricName, m, ptw)
    new GenStaticReduce(m, active, ptw, rule, this, metricName).emitRule()
  }

  def incMetric(metric: String, m: MethodDSL, ptw: VarIdx): Unit =
    if(config.collectStats) m.aload(ptw).ldc(metric).iconst(1).invoke(ptw_recordMetric)

  private def compileCell(sk: SymbolKind): Unit = {
    val payloadInterfaces = sk.boxType match {
      case "I" => Vector(intBoxT.className)
      case "R" => Vector(refBoxT.className)
      case _ => Vector.empty
    }
    val c = DSL.newClass(Acc.PUBLIC.FINAL, concreteCellTFor(sk).className, cellT, payloadInterfaces.toArray)

    val (cfields, pfields) = (0 until sk.arity).map(i => (c.field(Acc.PUBLIC, s"acell$i", cellT), c.field(Acc.PUBLIC, s"aport$i", tp.I))).unzip

    {
      val m = c.method(Acc.PUBLIC.FINAL, cell_auxCell)
      val p1 = m.param("p1", tp.I)
      sk.arity match {
        case 0 => m.aconst_null.areturn
        case 1 => m.aload(m.receiver).getfield(cfields(0)).areturn
        case a => m.aload(m.receiver).iload(p1).tableSwitch(0 until a-1) { io => m.getfield(cfields(io.getOrElse(a-1))).areturn }
      }
    }

    {
      val m = c.method(Acc.PUBLIC.FINAL, cell_auxPort)
      val p1 = m.param("p1", tp.I)
      sk.arity match {
        case 0 => m.iconst(0).ireturn
        case 1 => m.aload(m.receiver).getfield(pfields(0)).ireturn
        case a => m.aload(m.receiver).iload(p1).tableSwitch(0 until a-1) { io => m.getfield(pfields(io.getOrElse(a-1))).ireturn }
      }
    }

    {
      val m = c.method(Acc.PUBLIC.FINAL, cell_setAux)
      val p1 = m.param("p1", tp.I)
      val c2 = m.param("c2", cellT)
      val p2 = m.param("p2", tp.I)
      sk.arity match {
        case 0 => m.return_
        case 1 => m.aload(m.receiver).dup.aload(c2).putfield(cfields(0)).iload(p2).putfield(pfields(0)).return_
        case a => m.aload(m.receiver).dup.iload(p1).tableSwitch(0 until a-1) { io =>
          val i = io.getOrElse(a-1)
          m.aload(c2).putfield(cfields(i)).iload(p2).putfield(pfields(i)).return_
        }
      }
    }

    // constructor
    {
      val params = tp.I +: ((0 until sk.arity).flatMap(_ => Seq(cellT, tp.I)))
      val m = c.constructor(Acc.PUBLIC, tp.m(params: _*))
      val symId = m.param(s"symId", tp.I)
      val aux = (0 until sk.arity).map(i => (m.param(s"c$i", cellT), m.param(s"p$i", tp.I)))
      m.aload(m.receiver).invokespecial(new_Cell)
      m.aload(m.receiver).iload(symId).putfield(cell_symId)
      aux.zip(cfields).zip(pfields).foreach { case (((auxc, auxp), cfield), pfield) =>
        m.aload(m.receiver).dup.aload(auxc).putfield(cfield).iload(auxp).putfield(pfield)
      }
      m.return_
    }

    // reinit
    {
      val m = c.method(Acc.PUBLIC, concreteReinitFor(sk))
      val aux = (0 until sk.arity).map(i => (m.param(s"c$i", cellT), m.param(s"p$i", tp.I)))
      aux.zip(cfields).zip(pfields).foreach { case (((auxc, auxp), cfield), pfield) =>
        m.aload(m.receiver).dup.aload(auxc).putfield(cfield).iload(auxp).putfield(pfield)
      }
      m.return_
    }

    // payload implementation
    if(sk.boxType != "V") {
      val field = concretePayloadFieldFor(sk)
      c.field(Acc.PUBLIC, field)
      c.setter(field)
      c.getter(field)
    }

    addClass(classWriter, c)
  }

  private def compileMetaClass(sym: Symbol): Unit = {
    val rulePairs = rules.keys.iterator.collect {
      case rk if rk.sym1 == sym => (rk.sym2, rk)
      case rk if rk.sym2 == sym => (rk.sym1, rk)
    }.toMap

    val c = DSL.newClass(Acc.PUBLIC.FINAL, concreteMetaClassTFor(sym).className, metaClassT)

    c.field(Acc.PUBLIC.STATIC.FINAL, metaClass_singleton(sym))

    // constructor
    {
      val m = c.constructor(Acc.PRIVATE, tp.m())
      m.aload(m.receiver)
      reifySymbol(m, sym)
      m.iconst(symIds(sym))
      m.invokespecial(new_MetaClass)
      m.return_
    }

    // class init
    if(sym.isSingleton) {
      val f = c.field(Acc.PUBLIC.STATIC.FINAL, metaClass_singletonCell(sym))
      val m = c.clinit()
      m.newInitDup(concreteMetaClassTFor(sym).constr(tp.m().V))().putstatic(metaClass_singleton(sym))
      m.newInitDup(concreteConstrFor(sym)) { m.iconst(symIds(sym)) }.putstatic(f)
      m.return_
    } else {
      c.clinit().newInitDup(concreteMetaClassTFor(sym).constr(tp.m().V))().putstatic(metaClass_singleton(sym)).return_
    }

    addClass(classWriter, c)
  }

  private def compileDispatch(): Unit = {
    val c = DSL.newClass(Acc.PUBLIC.FINAL, generatedDispatchT.className, dispatchT)
    c.emptyNoArgsConstructor()

    def mkRuleKey(s1: Int, s2: Int): Int = (s1 << symBits) | s2

    val m = c.method(Acc.PUBLIC.FINAL, dispatch_reduce)
    val c1 = m.param("c1", cellT)
    val c2 = m.param("c2", cellT)
    val ptw = m.param("ptw", ptwT)

    m.aload(c1).getfield(cell_symId).iconst(symBits).ishl
    m.aload(c2).getfield(cell_symId).ior

    val keys = rules.flatMap { case (rk, rp) if !rp.initial =>
      Iterator(
        (mkRuleKey(symIds(rk.sym1), symIds(rk.sym2)), (rk, m.newLabel, false)),
        (mkRuleKey(symIds(rk.sym2), symIds(rk.sym1)), (rk, m.newLabel, true))
      )
    }.toVector.sortBy(_._1)
    val dflt = m.newLabel
    m.lookupswitch(keys.iterator.map(_._1).toArray, dflt, keys.map(_._2._2))
    keys.foreach { case (_, (rk, l, rev)) =>
      m.setLabel(l)
      val staticMR = ruleT_static_reduce(rk.sym1, rk.sym2)
      if(rev) {
        m.aload(c2).checkcast(concreteCellTFor(rk.sym1))
        m.aload(c1).checkcast(concreteCellTFor(rk.sym2))
      } else {
        m.aload(c1).checkcast(concreteCellTFor(rk.sym1))
        m.aload(c2).checkcast(concreteCellTFor(rk.sym2))
      }
      m.aload(ptw).invokestatic(staticMR)
      m.return_
    }
    m.setLabel(dflt)
    m.aload(ptw).aload(c1).aload(c2).invoke(ptw_addIrreducible)
    m.return_

    addClass(classWriter, c)
  }

  // find symbols that can interact with every symbol (usually dup & erase)
  private def findCommonPartners(): Set[Symbol] = {
    val ruleMap = mutable.HashMap.empty[Symbol, mutable.HashSet[Symbol]]
    rules.foreach { case (k, _) =>
      ruleMap.getOrElseUpdate(k.sym1, mutable.HashSet.empty) += k.sym2
      ruleMap.getOrElseUpdate(k.sym2, mutable.HashSet.empty) += k.sym1
    }
    if(config.allCommon) ruleMap.keySet.toSet
    else {
      val totalSyms = ruleMap.size
      val counts = mutable.HashMap.empty[Symbol, Int]
      for {
        v <- ruleMap.valuesIterator
        s <- v
      } {
        counts.updateWith(s) {
          case None => Some(1)
          case Some(x) => Some(x+1)
        }
      }
      counts.iterator.filter(_._2 == totalSyms).map(_._1).toSet
    }
  }

  private def compileCellCache(): Unit = {
    val syms = ((for {
      r <- rules.valuesIterator
      b <- r.branches.iterator
      s <- b.cellSyms.iterator
    } yield s) ++ (rules.keysIterator.map(_.sym1) ++ rules.keysIterator.map(_.sym2)).filter(_.isDefined)).toVector.distinct.sortBy(_.id)
    val c = DSL.newClass(Acc.PUBLIC.FINAL, cellCacheT.className)
    c.emptyNoArgsConstructor(Acc.PRIVATE)
    syms.foreach { sym => c.field(Acc.PRIVATE.STATIC, cellCache_var(sym)) }
    syms.foreach { sym =>
      val m = c.method(Acc.PUBLIC.STATIC.FINAL, cellCache_get(sym))
      val f = cellCache_var(sym)
      m.getstatic(f).aconst_null.putstatic(f).areturn
    }
    syms.foreach { sym =>
      val m = c.method(Acc.PUBLIC.STATIC.FINAL, cellCache_set(sym))
      val cell = m.param("cell", concreteCellTFor(sym))
      m.aload(cell).putstatic(cellCache_var(sym)).return_
    }
    addClass(classWriter, c)
  }

  private def compileInitial(rule: RulePlan, initialIndex: Int): String = {
    val staticMR = initialRuleT_static_reduce(initialIndex)
    val c = DSL.newClass(Acc.PUBLIC.FINAL, staticMR.owner.className, riT)
    c.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(c, rule, staticMR)

    // reduce
    {
      val m = c.method(Acc.PUBLIC.FINAL, ri_reduce)
      val c1 = m.param("c1", cellT)
      val c2 = m.param("c2", cellT)
      val ptw = m.param("ptw", ptwT)
      m.aload(c1).aload(c2).aload(ptw).invokestatic(staticMR).return_
    }

    val freeSymFields = rule.initialSyms.get.zipWithIndex.map { case (sym, i) =>
      (sym, c.field(Acc.PRIVATE.STATIC.FINAL, s"freeSym$i", AbstractCodeGen.symbolT))
    }

    // clinit
    {
      val m = c.clinit()
      freeSymFields.foreach { case (sym, f) => reifySymbol(m, sym).putstatic(f) }
      m.return_
    }

    // freeWires
    {
      val m = c.method(Acc.PUBLIC.FINAL, ri_freeWires)
      m.iconst(freeSymFields.length)
      m.newarray(AbstractCodeGen.symbolT)
      freeSymFields.zipWithIndex.foreach { case ((sym, f), i) => m.dup.iconst(i).getstatic(f).aastore }
      m.areturn
    }

    addClass(classWriter, c)
    c.javaName
  }

  private def compileRule(rule: RulePlan): Unit = {
    val staticMR = ruleT_static_reduce(rule.sym1, rule.sym2)
    val ric = DSL.newClass(Acc.PUBLIC.FINAL, staticMR.owner.className)
    ric.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(ric, rule, staticMR)
    addClass(classWriter, ric)
  }

  def compile(): (Vector[String], String) = {
    val constrs = globals.symbols.filter(_.isCons).toVector.sortBy(_.id)
    compileDispatch()
    if(config.useCellCache) compileCellCache()
    val symKinds = constrs.iterator.map(SymbolKind(_)).toSet
    ParSupport.foreach(symKinds, config.compilerParallelism)(compileCell)
    ParSupport.foreach(constrs, config.compilerParallelism)(compileMetaClass)
    ParSupport.foreach(rules.values.toVector.sortBy(_.key.toString), config.compilerParallelism)(compileRule)
    val irs = (compilationUnit.statements.iterator.collect { case i: RulePlan if i.initial => i }).zipWithIndex.map { case (ip, i) =>
      compileInitial(ip, i)
    }.toVector
    (irs, generatedDispatchT.javaName)
  }
}

final class ActiveCell(val id: Int, val vidx: VarIdx, val sym: Symbol, val arity: Int, val needsCachedPayload: Boolean) {
  var reuse: Int = -1
  var cachedPayload: VarIdx = VarIdx.none
}
