package de.szeiger.interact.stc2

import de.szeiger.interact.codegen.{AbstractCodeGen, ClassWriter, ParSupport}
import de.szeiger.interact.{Config, LifecycleManaged, RulePlan}
import de.szeiger.interact.ast.{CompilationUnit, Symbol, Symbols}
import de.szeiger.interact.codegen.AbstractCodeGen.{encodeName, symbolT}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}
import de.szeiger.interact.offheap.{Allocator, MemoryDebugger}

import Interpreter._

class CodeGen(genPackage: String, classWriter: ClassWriter,
  compilationUnit: CompilationUnit, globals: Symbols, val symIds: Map[Symbol, Int], val config: Config) extends AbstractCodeGen(config) { self =>

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
  val ptw_recordStats = ptwT.method("recordStats", tp.m(tp.I, tp.I, tp.I, tp.I, tp.I, tp.I, tp.I, tp.I, tp.I, tp.I).V)
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
  val staticReduceName = "static_reduce"
  val staticReduceDesc = tp.m(cellT, cellT, tp.I, ptwT).V
  val unboxedStaticReduceName = "unboxed_static_reduce"
  val generatedDispatch_staticReduce = generatedDispatchT.method(staticReduceName, staticReduceDesc)
  def ruleT(sym1: Symbol, sym2: Symbol) = tp.c(s"$genPackage/Rule_${encodeName(sym1)}$$_${encodeName(sym2)}")
  def initialRuleT(idx: Int) = tp.c(s"$genPackage/InitialRule_$idx")
  def concreteMetaClassTFor(sym: Symbol) = if(sym.isDefined) tp.c(s"$genPackage/M_${encodeName(sym)}") else metaClassT
  def metaClass_singleton(sym: Symbol) = { val tp = concreteMetaClassTFor(sym); tp.field("singleton", tp) }
  def metaClass_reduce(sym: Symbol) = concreteMetaClassTFor(sym).method("reduce", tp.m(cellT, cellT, tp.I, ptwT).V)

  val rules = compilationUnit.statements.collect { case g: RulePlan if !g.initial => (g.key, g) }.toMap

  def shouldUnbox(sym: Symbol, arity: Int = -1) =
    config.unboxedPrimitives && Interpreter.canUnbox(sym, if(arity == -1) sym.arity else arity)

  private def implementStaticReduce(classDSL: ClassDSL, rule: RulePlan): Unit = {
    val needsCachedPayloads = rule.branches.iterator.flatMap(_.needsCachedPayloads).toSet
    class P(val idx: Int, val sym: Symbol, val arity: Int) {
      val unbox = shouldUnbox(sym, arity)
      val unboxedVoid = unbox && sym.payloadType.isEmpty
      val name = if(sym.isDefined) AbstractCodeGen.encodeName(sym) else s"initial$idx"
      val t = if(!unbox) cellT else PTOps(null, sym.payloadType)(self).unboxedT
      def ac(m: MethodDSL) = {
        if(unbox) {
          val ac = new ActiveCell(m, self, 0, VarIdx.none, sym, arity, !unboxedVoid, unbox, name)
          if(!unboxedVoid) ac.cachedPayload = m.param(s"payload${idx}_$name", t)
          ac
        } else new ActiveCell(m, self, 0, m.param(s"ac${idx}_$name", t), sym, arity, needsCachedPayloads.contains(idx), unbox, name)
      }
    }
    val p0 = new P(0, rule.sym1, rule.arity1)
    val p1 = new P(1, rule.sym2, rule.arity2)
    val (unboxed, name) = if(p0.unbox || p1.unbox) (true, unboxedStaticReduceName) else (false, staticReduceName)
    val staticReduceDesc = tp.m(Seq(p0.t, p1.t, tp.I, ptwT).filter(_ != tp.V): _*).V
    lazy val m = classDSL.method(Acc.PUBLIC.STATIC, name, staticReduceDesc, debugLineNumbers = true)
    val active = Vector(p0.ac(m), p1.ac(m))
    val level = m.param("level", tp.I)
    val ptw = m.param("ptw", ptwT)
    val metricName = s"${classDSL.name}.${m.name}"
    incMetric(metricName, m, ptw)
    new GenStaticReduce(m, active, level, ptw, rule, this, metricName).emitRule()
    if(unboxed) implementStaticReduceUnboxingBridge(classDSL, rule, staticReduceDesc)
  }

  private def implementStaticReduceUnboxingBridge(classDSL: ClassDSL, rule: RulePlan, unboxedDesc: MethodDesc): Unit = {
    val m = classDSL.method(Acc.PUBLIC.STATIC, staticReduceName, staticReduceDesc)
    val ac0 = m.param(s"ac0", cellT)
    val ac1 = m.param(s"ac0", cellT)
    val level = m.param("level", tp.I)
    val ptw = m.param("ptw", ptwT)
    def unbox(sym: Symbol, arity: Int, ac: VarIdx) =
      if(shouldUnbox(sym, arity)) {
        if(sym.payloadType.isDefined) {
          val pt = PTOps(m, sym.payloadType)(this)
          pt.untag(m.lload(ac))
        }
      } else m.lload(ac)
    unbox(rule.sym1, rule.arity1, ac0)
    unbox(rule.sym2, rule.arity2, ac1)
    m.iload(level).aload(ptw).invokestatic(classDSL.thisTp, unboxedStaticReduceName, unboxedDesc).return_
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
      val m = c.method(Acc.PUBLIC.STATIC.FINAL, mref.name, mref.desc, debugLineNumbers = true)
      val c1 = m.param("c1", cellT)
      val c2 = m.param("c2", cellT)
      val level = m.param("level", tp.I)
      val ptw = m.param("ptw", ptwT)

      incMetric(s"${c.name}.${m.name}", m, ptw)

      if(config.unboxedPrimitives) {
        m.lload(c2).dup2.lconst(TAGMASK).land.lconst(TAG_UNBOXED).lcmp.if_==.thnElse {
          m.lconst(SYMIDMASK).land.l2i
        } {
          m.invokestatic(allocator_getInt)
        }
      } else {
        m.lload(c2).invokestatic(allocator_getInt)
      }
      m.iconst(TAGWIDTH).iushr

      val keys = rules.iterator.flatMap {
        case (rk, rp) if rk.sym1 == sym && !rp.initial => Iterator( (rk, symIds(rk.sym2), m.newLabel, false) )
        case (rk, rp) if rk.sym2 == sym && !rp.initial => Iterator( (rk, symIds(rk.sym1), m.newLabel, true) )
        case _ => Iterator.empty
      }.toVector.sortBy(_._2)
      val dflt = m.newLabel
      m.tableswitchOpt(keys.iterator.map(_._2).toArray, dflt, keys.map(_._3))
      keys.foreach { case (rk, _, l, rev) =>
        m.setLabel(l)
        val staticMR = ruleT(rk.sym1, rk.sym2).method(staticReduceName, staticReduceDesc)
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
      val m = c.method(Acc.PUBLIC.STATIC.FINAL, generatedDispatch_staticReduce.name, generatedDispatch_staticReduce.desc, debugLineNumbers = true)
      val c1 = m.param("c1", cellT)
      val c2 = m.param("c2", cellT)
      val level = m.param("level", tp.I)
      val ptw = m.param("ptw", ptwT)

      val syms = rules.iterator.flatMap { case (rk, rp) if !rp.initial => Iterator(rk.sym1, rk.sym2) }.toSet
      val keys = syms.iterator.map { sym => (symIds(sym), sym, m.newLabel) }.toVector.sortBy(_._1)
      val dflt = m.newLabel

      incMetric(s"${c.name}.${m.name}", m, ptw)

      m.lload(c1).lload(c2).iload(level).aload(ptw)

      if(config.unboxedPrimitives) {
        m.lload(c1).dup2.lconst(TAGMASK).land.lconst(TAG_UNBOXED).lcmp.if_==.thnElse {
          m.lconst(SYMIDMASK).land.l2i
        } {
          m.invokestatic(allocator_getInt)
        }
      } else {
        m.lload(c1).invokestatic(allocator_getInt)
      }
      m.iconst(TAGWIDTH).iushr

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

  private def compileInitial(rule: RulePlan, initialIndex: Int): String = {
    val staticMR = initialRuleT(initialIndex).method(staticReduceName, staticReduceDesc)
    val c = DSL.newClass(Acc.PUBLIC.FINAL, staticMR.owner.className, riT)
    c.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(c, rule)

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
    val ric = DSL.newClass(Acc.PUBLIC.FINAL, ruleT(rule.sym1, rule.sym2).className)
    ric.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(ric, rule)
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

final class ActiveCell(m: MethodDSL, cg: CodeGen, val id: Int, val vidx: VarIdx, val sym: Symbol, val arity: Int, val needsCachedPayload: Boolean,
  val unboxed: Boolean, val encName: String) {
  var reuse: Int = -1
  var cachedPayload: VarIdx = VarIdx.none
  var cachedPayloadProxyPage: VarIdx = VarIdx.none
  var cachedPayloadProxyPageOffset: VarIdx = VarIdx.none
  val pt: PTOps = if(unboxedParameter) PTOps(m, sym.payloadType)(cg) else null

  def unboxedParameter = vidx.isEmpty
  def unboxedVoid = unboxedParameter && sym.payloadType.isEmpty

  override def toString = s"ac$id(vidx=$vidx, sym=$sym, arity=$arity, needsCP=$needsCachedPayload, unboxed=$unboxed, reuse=$reuse)"
}
