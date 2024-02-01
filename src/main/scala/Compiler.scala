package de.szeiger.interact

import de.szeiger.interact.ast._

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
  )

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

  private[this] val rulePlans = mutable.Map.empty[RuleKey, RuleWiring]
  private[this] val data = mutable.ArrayBuffer.empty[Let]
  private[this] val initialPlans = mutable.ArrayBuffer.empty[InitialRuleWiring]
  unit.statements.foreach {
    case i: InitialRuleWiring => initialPlans += i
    case l: Let => data += l
    case g: RuleWiring =>
      val key = new RuleKey(g.sym1, g.sym2)
      if(rulePlans.put(key, g).isDefined) error(s"Duplicate rule ${g.sym1} <-> ${g.sym2}", g)
  }
  checkThrow()

  def createInterpreter(config: Config = global.config): BaseInterpreter =
    if(config.multiThreaded) new mt.Interpreter(globalSymbols, rulePlans.values, config, data, initialPlans)
    else new st.Interpreter(globalSymbols, rulePlans, config, initialPlans)
}

final class RuleKey(val sym1: Symbol, val sym2: Symbol) {
  override def equals(o: Any): Boolean = o match {
    case o: RuleKey => o.sym1 == sym1 && o.sym2 == sym2 || o.sym1 == sym2 && o.sym2 == sym1
    case _ => false
  }
  override def hashCode(): Int = sym1.hashCode() + sym2.hashCode()
  override def toString: String = s"$sym1 <-> $sym2"
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
  inlineUniqueContinuations: Boolean = true, // st.c
  reuseCells: Boolean = true, // st.c
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
