package de.szeiger.interact.stc2

import de.szeiger.interact.codegen.{AbstractCodeGen, ClassWriter, ParSupport}
import de.szeiger.interact.{Config, LifecycleManaged, RulePlan}
import de.szeiger.interact.ast.{CompilationUnit, Symbol, Symbols}
import de.szeiger.interact.codegen.AbstractCodeGen.{encodeName, symbolT}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import de.szeiger.interact.offheap.{Allocator, MemoryDebugger}

import scala.collection.mutable

import Interpreter._

class CodeGen(genPackage: String, classWriter: ClassWriter,
  compilationUnit: CompilationUnit, globals: Symbols, val symIds: Map[Symbol, Int], val config: Config) extends AbstractCodeGen(config) {

  val riT = tp.c[InitialRuleImpl]
  val ptwT = tp.c[Interpreter]
  val cellT = tp.J
  val allocatorT = if(config.debugMemory) tp.c(tp.c[MemoryDebugger.type].className.dropRight(1)) else tp.c[Allocator]
  val metaClassT = tp.c[MetaClass]
  val dispatchT = tp.c[Dispatch]
  val lifecycleManagedT = tp.i[LifecycleManaged]
  val generatedDispatchT = tp.c(s"$genPackage/Dispatch")

  val dispatch_reduce = dispatchT.method("reduce", tp.m(cellT, cellT, tp.I, ptwT).V)
  val ri_reduce = riT.method("reduce", tp.m(cellT, cellT, ptwT).V)
  val ri_freeWires = riT.method("freeWires", tp.m()(symbolT.a))
  val metaClass_symId = metaClassT.field("symId", tp.I)
  val allocator_putInt = allocatorT.method("putInt", tp.m(tp.J, tp.I).V)
  val allocator_getInt = allocatorT.method("getInt", tp.m(tp.J).I)
  val allocator_putLong = allocatorT.method("putLong", tp.m(tp.J, tp.J).V)
  val allocator_getLong = allocatorT.method("getLong", tp.m(tp.J).J)
  val allocator_getObject = allocatorT.method("getObject", tp.m(tp.Object, tp.J)(tp.Object))
  val allocator_putObject = allocatorT.method("putObject", tp.m(tp.Object, tp.J, tp.Object).V)
  val ptw_addActive = ptwT.method("addActive", tp.m(cellT, cellT).V)
  val ptw_recordStats = ptwT.method("recordStats", tp.m(tp.I, tp.I, tp.I, tp.I, tp.I, tp.I, tp.I, tp.I, tp.I).V)
  val ptw_recordMetric = ptwT.method("recordMetric", tp.m(tp.c[String], tp.I).V)
  val ptw_addIrreducible = ptwT.method("addIrreducible", tp.m(cellT, cellT).V)
  val ptw_getSingleton = ptwT.method("getSingleton", tp.m(tp.I)(cellT))
  val ptw_allocCell = ptwT.method("allocCell", tp.m(tp.I)(cellT))
  val ptw_freeCell = ptwT.method("freeCell", tp.m(cellT, tp.I).V)
  def ptw_allocSpec(size: Int) = ptwT.method(s"alloc$size", tp.m()(cellT))
  def ptw_allocProxiedSpec(size: Int) = ptwT.method(s"alloc${size}p", tp.m()(cellT))
  def ptw_freeSpec(size: Int) = ptwT.method(s"free$size", tp.m(cellT).V)
  def ptw_freeProxiedSpec(size: Int) = ptwT.method(s"free${size}p", tp.m(cellT).V)
  val specializedCellAllocSizes = Set(8, 16, 24, 32)
  val ptw_newLabel = ptwT.method("newLabel", tp.m().J)
  val ptw_allocProxied = ptwT.method("allocProxied", tp.m(tp.I)(cellT))
  val ptw_freeProxied = ptwT.method("freeProxied", tp.m(cellT, tp.I).V)
  val ptw_getProxy = ptwT.method("getProxy", tp.m(tp.J)(tp.Object))
  val ptw_getProxyPage = ptwT.method("getProxyPage", tp.m(tp.J)(tp.Object))
  val ptw_setProxy = ptwT.method("setProxy", tp.m(tp.J, tp.Object).V)
  val lifecycleManaged_copy = lifecycleManagedT.method("copy", tp.m()(lifecycleManagedT))
  val new_MetaClass = metaClassT.constr(tp.m(symbolT, tp.I).V)
  val generatedDispatch_staticReduce = generatedDispatchT.method("staticReduce", tp.m(cellT, cellT, tp.I, ptwT).V)

  def ruleT_static_reduce(sym1: Symbol, sym2: Symbol) =
    tp.c(s"$genPackage/Rule_${encodeName(sym1)}$$_${encodeName(sym2)}").method("static_reduce", tp.m(cellT, cellT, tp.I, ptwT).V)
  def initialRuleT_static_reduce(idx: Int) =
    tp.c(s"$genPackage/InitialRule_$idx").method("static_reduce", tp.m(cellT, cellT, tp.I, ptwT).V)
  def concreteMetaClassTFor(sym: Symbol) = if(sym.isDefined) tp.c(s"$genPackage/M_${encodeName(sym)}") else metaClassT
  def metaClass_singleton(sym: Symbol) = { val tp = concreteMetaClassTFor(sym); tp.field("singleton", tp) }
  def metaClass_reduce(sym: Symbol) = concreteMetaClassTFor(sym).method("reduce", tp.m(cellT, cellT, tp.I, ptwT).V)

  val rules = compilationUnit.statements.collect { case g: RulePlan if !g.initial => (g.key, g) }.toMap

  private def implementStaticReduce(classDSL: ClassDSL, rule: RulePlan, mref: MethodRef): Unit = {
    val m = classDSL.method(Acc.PUBLIC.STATIC, mref.name, mref.desc, debugLineNumbers = true)
    val needsCachedPayloads = rule.branches.iterator.flatMap(_.needsCachedPayloads).toSet
    val active = Vector(
      new ActiveCell(0, m.param("active0", cellT), rule.sym1, rule.arity1, needsCachedPayloads.contains(0)),
      new ActiveCell(1, m.param("active1", cellT), rule.sym2, rule.arity2, needsCachedPayloads.contains(1)),
    )
    val level = m.param("level", tp.I)
    val ptw = m.param("ptw", ptwT)
    val metricName = s"${classDSL.name}.${m.name}"
    incMetric(metricName, m, ptw)
    new GenStaticReduce(m, active, level, ptw, rule, this, metricName).emitRule()
  }

  def incMetric(metric: String, m: MethodDSL, ptw: VarIdx, count: Int = 1): Unit =
    if(config.collectStats) m.aload(ptw).ldc(metric).iconst(count).invoke(ptw_recordMetric)

  private def compileMetaClass(sym: Symbol): Unit = {
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
    c.clinit().newInitDup(concreteMetaClassTFor(sym).constr(tp.m().V))().putstatic(metaClass_singleton(sym)).return_

    // static reduce
    {
      val mref = metaClass_reduce(sym)
      val m = c.method(Acc.PUBLIC.STATIC.FINAL, mref.name, mref.desc)
      val c1 = m.param("c1", cellT)
      val c2 = m.param("c2", cellT)
      val level = m.param("level", tp.I)
      val ptw = m.param("ptw", ptwT)

      m.lload(c2).invokestatic(allocator_getInt)

      val keys = rules.iterator.flatMap {
        case (rk, rp) if rk.sym1 == sym && !rp.initial => Iterator( (rk, mkHeader(symIds(rk.sym2)), m.newLabel, false) )
        case (rk, rp) if rk.sym2 == sym && !rp.initial => Iterator( (rk, mkHeader(symIds(rk.sym1)), m.newLabel, true) )
        case _ => Iterator.empty
      }.toVector.sortBy(_._2)
      val dflt = m.newLabel
      m.tableswitchOpt(keys.iterator.map(_._2).toArray, dflt, keys.map(_._3))
      keys.foreach { case (rk, _, l, rev) =>
        m.setLabel(l)
        val staticMR = ruleT_static_reduce(rk.sym1, rk.sym2)
        if(rev) m.lload(c2).lload(c1)
        else m.lload(c1).lload(c2)
        m.iload(level).aload(ptw).invokestatic(staticMR)
        m.return_
      }
      m.setLabel(dflt)
      m.aload(ptw).lload(c1).lload(c2).invoke(ptw_addIrreducible)
      m.return_
    }

    addClass(classWriter, c)
  }

  private def compileDispatch(): Unit = {
    val c = DSL.newClass(Acc.PUBLIC.FINAL, generatedDispatchT.className, dispatchT)
    c.emptyNoArgsConstructor()

    // staticReduce
    {
      val m = c.method(Acc.PUBLIC.STATIC.FINAL, generatedDispatch_staticReduce.name, generatedDispatch_staticReduce.desc)
      val c1 = m.param("c1", cellT)
      val c2 = m.param("c2", cellT)
      val level = m.param("level", tp.I)
      val ptw = m.param("ptw", ptwT)

      val syms = rules.iterator.flatMap { case (rk, rp) if !rp.initial => Iterator(rk.sym1, rk.sym2) }.toSet
      val keys = syms.iterator.map { sym => (mkHeader(symIds(sym)), sym, m.newLabel) }.toVector.sortBy(_._1)
      val dflt = m.newLabel

      m.lload(c1).lload(c2).iload(level).aload(ptw)
      m.lload(c1).invokestatic(allocator_getInt)
      m.tableswitchOpt(keys.iterator.map(_._1).toArray, dflt, keys.map(_._3))
      keys.foreach { case (_, sym, l) =>
        m.setLabel(l)
        m.invokestatic(metaClass_reduce(sym))
        m.return_
      }
      m.setLabel(dflt)
      m.aload(ptw).lload(c1).lload(c2).invoke(ptw_addIrreducible)
      m.return_
    }

    // reduce
    {
      val m = c.method(Acc.PUBLIC.FINAL, dispatch_reduce.name, dispatch_reduce.desc)
      val c1 = m.param("c1", cellT)
      val c2 = m.param("c2", cellT)
      val level = m.param("level", tp.I)
      val ptw = m.param("ptw", ptwT)
      m.lload(c1).lload(c2).iload(level).aload(ptw).invokestatic(generatedDispatch_staticReduce).return_
    }

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
      m.lload(c1).lload(c2).iconst(0).aload(ptw).invokestatic(staticMR).return_
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
  var cachedPayloadProxyPage: VarIdx = VarIdx.none
  var cachedPayloadProxyPageOffset: VarIdx = VarIdx.none
}
