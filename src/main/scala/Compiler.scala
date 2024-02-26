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
  ) ++ (if(config.backend.planRules) Vector(
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

  def createInterpreter(): BaseInterpreter = config.backend.createInterpreter(this)
}

trait Phase extends (CompilationUnit => CompilationUnit) {
  val global: Global
  val phaseName: String = getClass.getName.replaceAll(".*\\.", "")
  val phaseLogEnabled: Boolean = global.config.phaseLog.contains(phaseName) || global.config.phaseLog.contains("*")
  override def toString: String = phaseName

  @inline final def phaseLog(@inline msg: => String): Unit = if(phaseLogEnabled) global.phaseLog(phaseName, msg)
  @inline final def phaseLog(n: ShowableNode, name: String): Unit = if(phaseLogEnabled) global.phaseLog(phaseName, n, name)
}

case class Config(
  // Frontend
  defaultDerive: Seq[String] = Seq("erase", "dup"),
  addEraseDup: Boolean = true,
  phaseLog: Set[String] = Set.empty, // show debug log of these phases
  showAfter: Set[String] = Set.empty, // log AST after these phases
  inlineFull: Boolean = true, // inline rules that can be merged into a single branch
  inlineFullAll: Boolean = true, // inline simple matches even when duplicating a parent rule
  inlineBranching: Boolean = true, // inline rules that cannot be merged into a single branch (st.c)
  inlineUniqueContinuations: Boolean = true, // st.c

  // Backend
  backend: Backend = STC1Backend,
  numThreads: Int = 0, // mt
  collectStats: Boolean = false,
  useCellCache: Boolean = false, // stc*
  biasForCommonDispatch: Boolean = true, // optimize for invokevirtual dispatch of statically known cell types (stc1)
  logCodeGenSummary: Boolean = false, // stc*, mt.c
  logGeneratedClasses: Option[String] = None, // Log generated classes containing this string (stc*, mt.c)
  compilerParallelism: Int = 1,
  allCommon: Boolean = false, // compile all methods into CommonCell, not just shared ones (stc1)
  reuseCells: Boolean = true, // stc*
  reuseForeignSymbols: Boolean = true, // stc2
  writeOutput: Option[Path] = None, // write generated classes to dir or jar file (stc*)
  writeJava: Option[Path] = None, // write decompiled classes to dir (stc*)
  skipCodeGen: Boolean = false, // do not generate classfiles (stc*)
) {
  def withSpec(spec: String): Config = spec match {
    case s"sti" => copy(backend = STIBackend)
    case s"stc1" => copy(backend = STC1Backend)
    case s"stc2" => copy(backend = STC2Backend)
    case s"mt${mode}.i" => copy(backend = MTIBackend, numThreads = mode.toInt)
    case s"mt${mode}.c" => copy(backend = MTCBackend, numThreads = mode.toInt)
  }
}

abstract class Backend(val name: String) {
  def createInterpreter(comp: Compiler): BaseInterpreter
  def planRules: Boolean
  def inlineBranching: Boolean
  def inlineUniqueContinuations: Boolean
  def allowPayloadTemp: Boolean
  def reuseForeignSymbols: Boolean
}

object STIBackend extends Backend("sti") {
  def createInterpreter(comp: Compiler): BaseInterpreter =
    new sti.Interpreter(comp.global.globalSymbols, comp.unit, comp.global.config)
  def planRules: Boolean = false
  def inlineBranching: Boolean = false
  def inlineUniqueContinuations: Boolean = false
  def allowPayloadTemp: Boolean = false
  def reuseForeignSymbols: Boolean = false
}

object STC1Backend extends Backend("stc1") {
  def createInterpreter(comp: Compiler): BaseInterpreter =
    new stc1.Interpreter(comp.global.globalSymbols, comp.unit, comp.global.config)
  def planRules: Boolean = true
  def inlineBranching: Boolean = true
  def inlineUniqueContinuations: Boolean = true
  def allowPayloadTemp: Boolean = true
  def reuseForeignSymbols: Boolean = false
}

object STC2Backend extends Backend("stc2") {
  def createInterpreter(comp: Compiler): BaseInterpreter =
    new stc2.Interpreter(comp.global.globalSymbols, comp.unit, comp.global.config)
  def planRules: Boolean = true
  def inlineBranching: Boolean = true
  def inlineUniqueContinuations: Boolean = true
  def allowPayloadTemp: Boolean = true
  def reuseForeignSymbols: Boolean = true
}

class MTBackend(name: String, compile: Boolean) extends Backend(name) {
  def createInterpreter(comp: Compiler): BaseInterpreter = {
    import comp.global._
    val rulePlans = mutable.Map.empty[RuleKey, RuleWiring]
    val initialPlans = mutable.ArrayBuffer.empty[InitialRuleWiring]
    comp.unit.statements.foreach {
      case i: InitialRuleWiring => initialPlans += i
      case g: RuleWiring => rulePlans.put(g.key, g)
    }
    new mt.Interpreter(globalSymbols, rulePlans.values, config, mutable.ArrayBuffer.empty[Let], initialPlans, compile)
  }
  def planRules: Boolean = compile
  def inlineBranching: Boolean = compile
  def inlineUniqueContinuations: Boolean = compile
  def allowPayloadTemp: Boolean = compile
  def reuseForeignSymbols: Boolean = false
}

object MTIBackend extends MTBackend("mti", false)
object MTCBackend extends MTBackend("mti", true)

object Config {
  val defaultConfig: Config = Config()
  def apply(spec: String): Config = defaultConfig.withSpec(spec)
}
