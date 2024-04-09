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
  val staticReduceName = "reduce"
  val generatedDispatch_staticReduce = generatedDispatchT.method("static_reduce", tp.m(cellT, cellT, tp.I, ptwT).V)
  def ruleT(sym1: Symbol, sym2: Symbol) = tp.c(s"$genPackage/Rule_${encodeName(sym1)}$$_${encodeName(sym2)}")
  def initialRuleT(idx: Int) = tp.c(s"$genPackage/InitialRule_$idx")
  def concreteMetaClassTFor(sym: Symbol) = if(sym.isDefined) tp.c(s"$genPackage/M_${encodeName(sym)}") else metaClassT
  def metaClass_singleton(sym: Symbol) = { val tp = concreteMetaClassTFor(sym); tp.field("singleton", tp) }
  def metaClass_reduce(sym: Symbol) = concreteMetaClassTFor(sym).method("reduce", tp.m(cellT, cellT, tp.I, ptwT).V)
  def unboxedStaticReduceDesc(u0: Unboxing, u1: Unboxing) = tp.m(Seq(u0.paramT, u1.paramT, tp.I, ptwT).filter(_ != tp.V): _*).V

  val rules = compilationUnit.statements.collect { case g: RulePlan if !g.initial => (g.key, g) }.toMap

  class Unboxing private (val sym: Symbol, val arity: Int) {
    val unbox = shouldUnbox(sym, arity)
    val unboxedVoid = unbox && sym.payloadType.isEmpty
    val unboxedParamT = if(unbox) Some(ptOps(null).unboxedT) else None
    val paramT = unboxedParamT.getOrElse(cellT)
    def ptOps(m: MethodDSL) = PTOps(m, sym.payloadType)(self)
    def ldTaggedAsUntagged(m: MethodDSL, c: VarIdx): Unit = if(!unboxedVoid) {
      if(unbox) ptOps(m).untag(m.lload(c)) else m.lload(c)
    }
  }
  object Unboxing {
    private[this] val cache = mutable.HashMap.empty[(Symbol, Int), Unboxing]
    def apply(sym: Symbol): Unboxing = apply(sym, sym.arity)
    def apply(sym: Symbol, arity: Int): Unboxing = cache.getOrElseUpdate((sym, arity), new Unboxing(sym, arity))
  }

  def shouldUnbox(sym: Symbol, arity: Int = -1) =
    config.unboxedPrimitives && Interpreter.canUnbox(sym, if(arity == -1) sym.arity else arity)

  private def implementStaticReduce(classDSL: ClassDSL, rule: RulePlan): Unit = {
    val needsCachedPayloads = rule.branches.iterator.flatMap(_.needsCachedPayloads).toSet
    val u0 = Unboxing(rule.sym1, rule.arity1)
    val u1 = Unboxing(rule.sym2, rule.arity2)
    val desc = unboxedStaticReduceDesc(u0, u1)
    val m = classDSL.method(Acc.PUBLIC.STATIC, staticReduceName, desc, debugLineNumbers = true)
    def ac(idx: Int, u: Unboxing) = {
      val name = if(u.sym.isDefined) AbstractCodeGen.encodeName(u.sym) else s"initial$idx"
      if(u.unbox) {
        val ac = new ActiveCell(m, self, 0, VarIdx.none, u.sym, u.arity, !u.unboxedVoid, u.unbox, name)
        if(!u.unboxedVoid) ac.cachedPayload = m.param(s"ac${idx}u_$name", u.paramT)
        ac
      } else new ActiveCell(m, self, 0, m.param(s"ac${idx}_$name", u.paramT), u.sym, u.arity, needsCachedPayloads.contains(idx), u.unbox, name)
    }
    val active = Vector(ac(0, u0), ac(1, u1))
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
        case (rk, rp) if rk.sym1 == sym && !rp.initial => Iterator( (rk, symIds(rk.sym2), m.newLabel) )
        case (rk, rp) if rk.sym2 == sym && !rp.initial => Iterator( (rk, symIds(rk.sym1), m.newLabel) )
        case _ => Iterator.empty
      }.toVector.sortBy(_._2)
      val dflt = m.newLabel
      m.tableswitchOpt(keys.iterator.map(_._2).toArray, dflt, keys.map(_._3))
      keys.foreach { case (rk, _, l) =>
        m.setLabel(l)
        val u1 = Unboxing(rk.sym1)
        val u2 = Unboxing(rk.sym2)
        val (ca, cb) = if(rk.sym1 != sym) (c2, c1) else (c1, c2)
        u1.ldTaggedAsUntagged(m, ca)
        u2.ldTaggedAsUntagged(m, cb)
        m.iload(level).aload(ptw).invokestatic(ruleT(rk.sym1, rk.sym2).method(staticReduceName, unboxedStaticReduceDesc(u1, u2)))
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
    val u1 = Unboxing(rule.sym1, rule.arity1)
    val u2 = Unboxing(rule.sym2, rule.arity2)
    val staticMR = initialRuleT(initialIndex).method(staticReduceName, unboxedStaticReduceDesc(u1, u2))
    val c = DSL.newClass(Acc.PUBLIC.FINAL, staticMR.owner.className, riT)
    c.emptyNoArgsConstructor(Acc.PUBLIC)
    implementStaticReduce(c, rule)

    // reduce
    {
      val m = c.method(Acc.PUBLIC.FINAL, ri_reduce)
      val c1 = m.param("c1", cellT)
      val c2 = m.param("c2", cellT)
      val ptw = m.param("ptw", ptwT)
      u1.ldTaggedAsUntagged(m, c1)
      u2.ldTaggedAsUntagged(m, c2)
      m.iconst(0).aload(ptw).invokestatic(staticMR).return_
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
    ric.emptyNoArgsConstructor(Acc.PRIVATE)
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
