package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable

class Compiler(unit0: CompilationUnit, _fconfig: FrontendConfig = FrontendConfig()) {
  val global = new Global(_fconfig)
  import global._

  private[this] val phases: Vector[Phase] = Vector(
    new Prepare(global),
    new ExpandRules(global),
    new Curry(global),
    new CleanEmbedded(global),
    new ResolveEmbedded(global),
    new PlanRules(global),
    new Inline(global),
  )

  private[this] val unit1 = if(fconfig.addEraseDup) {
    val erase = globalSymbols.define("erase", isCons = true, isDef = true, returnArity = 0)
    val dup = globalSymbols.define("dup", isCons = true, isDef = true, arity = 2, returnArity = 2)
    unit0.copy(statements = Vector(DerivedRule(erase, erase), DerivedRule(erase, dup), DerivedRule(dup, dup)) ++ unit0.statements).setPos(unit0.pos)
  } else unit0

  val unit = phases.foldLeft(unit1) { case (u, p) =>
    val u2 = p(u)
    if(fconfig.showAfter.contains(p.phaseName) || fconfig.showAfter.contains("*"))
      ShowableNode.print(u2, name = s"After phase ${p.phaseName}")
    checkThrow()
    u2
  }

  private[this] val rulePlans = mutable.Map.empty[RuleKey, RulePlan]
  private[this] val data = mutable.ArrayBuffer.empty[Let]
  private[this] val initialPlans = mutable.ArrayBuffer.empty[InitialPlan]
  unit.statements.foreach {
    case i: InitialPlan => initialPlans += i
    case l: Let => data += l
    case g: RulePlan =>
      val key = new RuleKey(g.sym1, g.sym2)
      if(rulePlans.put(key, g).isDefined) error(s"Duplicate rule ${g.sym1} <-> ${g.sym2}", g)
  }
  checkThrow()

  def createMTInterpreter(bconfig: BackendConfig = BackendConfig()) : mt.Interpreter =
    new mt.Interpreter(globalSymbols, rulePlans.values, bconfig, data, initialPlans)

  def createSTInterpreter(bconfig: BackendConfig = BackendConfig()) : st.Interpreter =
    new st.Interpreter(globalSymbols, rulePlans, bconfig, initialPlans)

  def createInterpreter(spec: String, bconfig: BackendConfig = BackendConfig()): BaseInterpreter = {
    spec match {
      case s"st.i" => createSTInterpreter(bconfig.copy(compile = false))
      case s"st.c" => createSTInterpreter(bconfig.copy(compile = true))
      case s"mt${mode}.i" => createMTInterpreter(bconfig.copy(compile = false, numThreads = mode.toInt))
      case s"mt${mode}.c" => createMTInterpreter(bconfig.copy(compile = true, numThreads = mode.toInt))
    }
  }
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

case class FrontendConfig(
  defaultDerive: Seq[String] = Seq("erase", "dup"),
  addEraseDup: Boolean = true,
  showAfter: Set[String] = Set.empty, // log AST after these phases
)

case class BackendConfig(
  compile: Boolean = true,
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
)
