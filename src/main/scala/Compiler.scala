package de.szeiger.interact

import de.szeiger.interact.ast._

import java.nio.file.Path
import scala.collection.mutable

class Compiler(unit0: CompilationUnit, _config: Config = Config.defaultConfig) {
  val global = new Global(_config)
  import global._

  private[this] val phases: Vector[Phase] = Vector(
    new Prepare(global),
    new ExpandRules(global),
    new Curry(global),
    new CleanEmbedded(global),
    new ResolveEmbedded(global),
    new CreateWiring(global),
    new Inline(global),
  ) ++ (if(config.compile) Vector(
    new PlanRules(global),
  ) else Vector.empty)

  private[this] val unit1 = if(config.addEraseDup) {
    val erase = globalSymbols.define("erase", isCons = true, isDef = true, returnArity = 0)
    val dup = globalSymbols.define("dup", isCons = true, isDef = true, arity = 2, returnArity = 2, payloadType = PayloadType.LABEL)
    unit0.copy(statements = Vector(DerivedRule(erase, erase), DerivedRule(erase, dup), DerivedRule(dup, dup)) ++ unit0.statements).setPos(unit0.pos)
  } else unit0

  val unit = phases.foldLeft(unit1) { case (u, p) =>
    val u2 = p(u)
    if(config.showAfter.contains(p.phaseName) || config.showAfter.contains("*"))
      ShowableNode.print(u2, name = s"After phase ${p.phaseName}")
    checkThrow()
    u2
  }

  def createInterpreter(config: Config = global.config): BaseInterpreter =
    if(config.multiThreaded) {
      val rulePlans = mutable.Map.empty[RuleKey, RuleWiring]
      val initialPlans = mutable.ArrayBuffer.empty[InitialRuleWiring]
      unit.statements.foreach {
        case i: InitialRuleWiring => initialPlans += i
        case g: RuleWiring => rulePlans.put(g.key, g)
      }
      new mt.Interpreter(globalSymbols, rulePlans.values, config, mutable.ArrayBuffer.empty[Let], initialPlans)
    } else new st.Interpreter(globalSymbols, unit, config)
}

trait Phase extends (CompilationUnit => CompilationUnit) {
  def phaseName: String = getClass.getName.replaceAll(".*\\.", "")
  override def toString: String = phaseName
}

case class Config(
  // Frontend
  compile: Boolean = true,
  defaultDerive: Seq[String] = Seq("erase", "dup"),
  addEraseDup: Boolean = true,
  showAfter: Set[String] = Set.empty, // log AST after these phases
  inlineDuplicate: Boolean = false, // inline conditional circular dependencies from all starting rules
  inlineFull: Boolean = true, // inline rules that can be merged into a single branch
  inlineBranching: Boolean = true, // inline rules that cannot be merged into a single branch (st.c)
  inlineUniqueContinuations: Boolean = true, // st.c

  // Backend
  multiThreaded: Boolean = false,
  numThreads: Int = 0, // mt
  collectStats: Boolean = false,
  useCellCache: Boolean = false, // st.c
  biasForCommonDispatch: Boolean = true, // optimize for invokevirtual dispatch of statically known cell types (st.c)
  logCodeGenSummary: Boolean = false, // st.c, mt.c
  logGeneratedClasses: Option[String] = None, // Log generated classes containing this string (st.c, mt.c)
  compilerParallelism: Int = 1,
  allCommon: Boolean = false, // compile all methods into CommonCell, not just shared ones (st.c)
  reuseCells: Boolean = true, // st.c
  writeOutput: Option[Path] = None, // write generated classes to dir or jar file (st.c)
  writeJava: Option[Path] = None, // write decompiled classes to dir (st.c)
  skipCodeGen: Boolean = false, // do not generate classfiles (st.c)
) {
  def withSpec(spec: String): Config = spec match {
    case s"st.i" => copy(compile = false, multiThreaded = false)
    case s"st.c" => copy(compile = true, multiThreaded = false)
    case s"mt${mode}.i" => copy(compile = false, multiThreaded = true, numThreads = mode.toInt)
    case s"mt${mode}.c" => copy(compile = true, multiThreaded = true, numThreads = mode.toInt)
  }
}

object Config {
  val defaultConfig: Config = Config()
  def apply(spec: String): Config = defaultConfig.withSpec(spec)
}
