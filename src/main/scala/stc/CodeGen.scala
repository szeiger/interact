package de.szeiger.interact.stc

import de.szeiger.interact.codegen.{AbstractCodeGen, ClassWriter, ParSupport}
import de.szeiger.interact.{Config, IntBox, IntBoxImpl, PlanRules, RefBox, RefBoxImpl, RulePlan}
import de.szeiger.interact.ast.{CompilationUnit, PayloadType, Symbol, Symbols}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}

import scala.collection.mutable

class CodeGen(genPackage: String, classWriter: ClassWriter, val config: Config,
  compilationUnit: CompilationUnit, globals: Symbols) extends AbstractCodeGen(config) {

  import AbstractCodeGen.encodeName

  val riT = tp.c[InitialRuleImpl]
  val ptwT = tp.c[Interpreter]
  val cellT = tp.c[Cell]
  val intBoxT = tp.i[IntBox]
  val refBoxT = tp.i[RefBox]
  val intBoxImplT = tp.c[IntBoxImpl]
  val refBoxImplT = tp.c[RefBoxImpl]
  val commonCellT = tp.c(s"$genPackage/CommonCell")
  val cellCacheT = tp.c(s"$genPackage/CellCache")
  val ri_reduce = riT.method("reduce", tp.m(cellT, cellT, ptwT).V)
  val ri_freeWires = riT.method("freeWires", tp.m()(AbstractCodeGen.symbolT.a))
  val cell_reduce = cellT.method("reduce", tp.m(cellT, ptwT).V)
  val cell_arity = cellT.method("arity", tp.m().I)
  val cell_auxCell = cellT.method("auxCell", tp.m(tp.I)(cellT))
  val cell_auxPort = cellT.method("auxPort", tp.m(tp.I).I)
  val cell_setAux = cellT.method("setAux", tp.m(tp.I, cellT, tp.I).V)
  val cell_cellSymbol = cellT.method("cellSymbol", tp.m()(AbstractCodeGen.symbolT))
  val ptw_addActive = ptwT.method("addActive", tp.m(cellT, cellT).V)
  val ptw_recordStats = ptwT.method("recordStats", tp.m(tp.I, tp.I, tp.I, tp.I, tp.I, tp.I).V)
  val ptw_recordMetric = ptwT.method("recordMetric", tp.m(tp.c[String], tp.I).V)
  val ptw_addIrreducible = ptwT.method("addIrreducible", tp.m(cellT, cellT).V)
  val intBox_getValue = intBoxT.method("getValue", tp.m().I)
  val intBox_setValue = intBoxT.method("setValue", tp.m(tp.I).V)
  val refBox_getValue = refBoxT.method("getValue", tp.m()(tp.c[AnyRef]))
  val refBox_setValue = refBoxT.method("setValue", tp.m(tp.c[AnyRef]).V)
  val new_CommonCell = commonCellT.constr(tp.m().V)
  val new_IntBoxImpl = intBoxImplT.constr(tp.m().V)
  val new_RefBoxImpl = refBoxImplT.constr(tp.m().V)

  def ruleT_static_reduce(sym1: Symbol, sym2: Symbol) =
    tp.c(s"$genPackage/Rule_${encodeName(sym1)}$$_${encodeName(sym2)}").method("static_reduce", tp.m(concreteCellTFor(sym1), concreteCellTFor(sym2), ptwT).V)
  def initialRuleT_static_reduce(idx: Int) =
    tp.c(s"$genPackage/InitialRule_$idx").method("static_reduce", tp.m(cellT, cellT, ptwT).V)
  def interfaceT(sym: Symbol) = tp.i(s"$genPackage/I_${encodeName(sym)}")
  def interfaceMethod(sym: Symbol) = interfaceT(sym).method(s"reduce_${encodeName(sym)}", tp.m(concreteCellTFor(sym), ptwT).V)
  def concreteCellTFor(sym: Symbol) = if(sym.isDefined) tp.c(s"$genPackage/C_${encodeName(sym)}") else cellT
  def concreteConstrFor(sym: Symbol) = concreteCellTFor(sym).constr(tp.m((0 until sym.arity).flatMap(_ => Seq(cellT, tp.I)): _*).V)
  def concreteReinitFor(sym: Symbol) = concreteCellTFor(sym).method("reinit", tp.m((0 until sym.arity).flatMap(_ => Seq(cellT, tp.I)): _*).V)
  def concretePayloadFieldFor(sym: Symbol) = concreteCellTFor(sym).field("value", sym.payloadType match {
    case PayloadType.INT => tp.I
    case _ => tp.c[AnyRef]
  })
  def cell_acell(sym: Symbol, p: Int) = concreteCellTFor(sym).field(s"acell$p", cellT)
  def cell_aport(sym: Symbol, p: Int) = concreteCellTFor(sym).field(s"aport$p", tp.I)
  def cell_singleton(sym: Symbol) = { val tp = concreteCellTFor(sym); tp.field("singleton", tp) }
  def cellCache_var(sym: Symbol) = cellCacheT.field(s"f_${encodeName(sym)}", concreteCellTFor(sym))
  def cellCache_get(sym: Symbol) = cellCacheT.method(s"get_${encodeName(sym)}", tp.m()(concreteCellTFor(sym)))
  def cellCache_set(sym: Symbol) = cellCacheT.method(s"set_${encodeName(sym)}", tp.m(concreteCellTFor(sym)).V)

  val rules = compilationUnit.statements.collect { case g: RulePlan if !g.initial => (g.key, g) }.toMap
  val common = findCommonPartners()

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

  private def compileInterface(sym: Symbol): Unit = {
    val ifm = interfaceMethod(sym)
    val c = DSL.newInterface(Acc.PUBLIC, ifm.owner.className)
    c.method(Acc.PUBLIC.ABSTRACT, ifm.name, ifm.desc)
    addClass(classWriter, c)
  }

  private def compileCell(sym: Symbol): Unit = {
    val rulePairs = rules.keys.iterator.collect {
      case rk if rk.sym1 == sym => (rk.sym2, rk)
      case rk if rk.sym2 == sym => (rk.sym1, rk)
    }.toMap
    val interfaces = (rulePairs.keySet -- common).iterator.map(s => interfaceT(s).className).toArray.sorted
    val payloadInterfaces = sym.payloadType match {
      case PayloadType.INT => Vector(intBoxT.className)
      case PayloadType.REF | PayloadType.LABEL => Vector(refBoxT.className)
      case _ => Vector.empty
    }
    val c = DSL.newClass(Acc.PUBLIC.FINAL, concreteCellTFor(sym).className, commonCellT, interfaces ++ payloadInterfaces)

    val (cfields, pfields) = (0 until sym.arity).map(i => (c.field(Acc.PUBLIC, s"acell$i", cellT), c.field(Acc.PUBLIC, s"aport$i", tp.I))).unzip
    val symField = c.field(Acc.PRIVATE.STATIC, "cellSymbol", AbstractCodeGen.symbolT)

    // accessors
    c.method(Acc.PUBLIC.FINAL, cell_arity).iconst(sym.arity).ireturn

    {
      val m = c.method(Acc.PUBLIC.FINAL, cell_auxCell)
      val p1 = m.param("p1", tp.I)
      sym.arity match {
        case 0 => m.aconst_null.areturn
        case 1 => m.aload(m.receiver).getfield(cfields(0)).areturn
        case a => m.aload(m.receiver).iload(p1).tableSwitch(0 until a-1) { io => m.getfield(cfields(io.getOrElse(a-1))).areturn }
      }
    }

    {
      val m = c.method(Acc.PUBLIC.FINAL, cell_auxPort)
      val p1 = m.param("p1", tp.I)
      sym.arity match {
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
      sym.arity match {
        case 0 => m.return_
        case 1 => m.aload(m.receiver).dup.aload(c2).putfield(cfields(0)).iload(p2).putfield(pfields(0)).return_
        case a => m.aload(m.receiver).dup.iload(p1).tableSwitch(0 until a-1) { io =>
          val i = io.getOrElse(a-1)
          m.aload(c2).putfield(cfields(i)).iload(p2).putfield(pfields(i)).return_
        }
      }
    }

    c.method(Acc.PUBLIC.FINAL, cell_cellSymbol).getstatic(symField).areturn

    // constructor
    {
      val params = (0 until sym.arity).flatMap(_ => Seq(cellT, tp.I))
      val m = c.constructor(if(sym.isSingleton) Acc.PRIVATE else Acc.PUBLIC, tp.m(params: _*))
      val aux = (0 until sym.arity).map(i => (m.param(s"c$i", cellT), m.param(s"p$i", tp.I)))
      m.aload(m.receiver).invokespecial(new_CommonCell)
      aux.zip(cfields).zip(pfields).foreach { case (((auxc, auxp), cfield), pfield) =>
        m.aload(m.receiver).dup.aload(auxc).putfield(cfield).iload(auxp).putfield(pfield)
      }
      m.return_
      if(sym.isSingleton) c.field(Acc.PUBLIC.STATIC.FINAL, cell_singleton(sym))
    }

    // class init
    {
      val m = c.clinit()
      if(sym.isSingleton) m.newInitDup(concreteConstrFor(sym))().putstatic(cell_singleton(sym))
      reifySymbol(m, sym).putstatic(symField)
      m.return_
    }

    // reinit
    if(sym.arity > 0 || sym.payloadType.isDefined) {
      val m = c.method(Acc.PUBLIC, concreteReinitFor(sym))
      val aux = (0 until sym.arity).map(i => (m.param(s"c$i", cellT), m.param(s"p$i", tp.I)))
      aux.zip(cfields).zip(pfields).foreach { case (((auxc, auxp), cfield), pfield) =>
        m.aload(m.receiver).dup.aload(auxc).putfield(cfield).iload(auxp).putfield(pfield)
      }
      m.return_
    }

    // payload implementation
    if(sym.payloadType.isDefined) {
      val field = concretePayloadFieldFor(sym)
      c.field(Acc.PUBLIC, field)
      c.setter(field)
      c.getter(field)
    }

    // generic reduce
    {
      val m = c.method(Acc.PUBLIC.FINAL, cell_reduce.name, cell_reduce.desc)
      val other = m.param("other", cellT)
      val ptw = m.param("ptw", ptwT)
      incMetric(s"${c.name}.${m.name}", m, ptw)
      val isShared = common.contains(sym)
      val ifm = if(isShared) interfaceMethod(sym).on(commonCellT) else interfaceMethod(sym)
      m.aload(other)
      m.tryCatchGoto(tp.c[ClassCastException]) {
        m.checkcast(ifm.owner)
      } {
        m.pop
        m.aload(ptw).aload(m.receiver).aload(other).invoke(ptw_addIrreducible)
        m.return_
      }
      m.aload(m.receiver).aload(ptw)
      m.invoke(ifm)
      m.return_
    }

    // interface methods
    rulePairs.toVector.sortBy(_._1.id).foreach { case (sym2, rk) =>
      val ifm = interfaceMethod(sym2)
      val m = c.method(Acc.PUBLIC.FINAL, ifm.name, ifm.desc)
      val other = m.param("other", concreteCellTFor(sym2))
      val ptw = m.param("ptw", ptwT)
      incMetric(s"${c.name}.${m.name}", m, ptw)
      val staticMR = ruleT_static_reduce(rk.sym1, rk.sym2)
      if(rk.sym1 == sym) m.aload(m.receiver).aload(other)
      else m.aload(other).aload(m.receiver)
      m.aload(ptw).invokestatic(staticMR).return_
    }
    // unsupported common operations (when using config.allCommon)
    (common -- rulePairs.keySet).toVector.sortBy(_.id).foreach { sym2 =>
      val ifm = interfaceMethod(sym2)
      val m = c.method(Acc.PUBLIC.FINAL, ifm.name, ifm.desc)
      val other = m.param("other", concreteCellTFor(sym2))
      val ptw = m.param("ptw", ptwT)
      m.aload(ptw).aload(m.receiver).aload(other).invoke(ptw_addIrreducible).return_
    }
    addClass(classWriter, c)
  }

  private def compileCommonCell(): Unit = {
    val c = DSL.newClass(Acc.PUBLIC.ABSTRACT, commonCellT.className, cellT)
    c.emptyNoArgsConstructor(Acc.PROTECTED)
    common.foreach(sym => c.method(Acc.PUBLIC.ABSTRACT, interfaceMethod(sym)))
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

  def compile(): Vector[String] = {
    ParSupport.foreach(globals.symbols.filter(s => s.isCons && !common.contains(s)).toVector.sortBy(_.id), config.compilerParallelism)(compileInterface)
    compileCommonCell()
    if(config.useCellCache) compileCellCache()
    ParSupport.foreach(globals.symbols.filter(_.isCons).toVector.sortBy(_.id), config.compilerParallelism)(compileCell)
    ParSupport.foreach(rules.values.toVector.sortBy(_.key.toString), config.compilerParallelism)(compileRule)
    (compilationUnit.statements.iterator.collect { case i: RulePlan if i.initial => i }).zipWithIndex.map { case (ip, i) =>
      compileInitial(ip, i)
    }.toVector
  }
}

final class ActiveCell(val id: Int, val vidx: VarIdx, val sym: Symbol, val arity: Int, val needsCachedPayload: Boolean) {
  var reuse: Int = -1
  var cachedPayload: VarIdx = VarIdx.none
}
