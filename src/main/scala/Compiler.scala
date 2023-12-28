package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable

class Compiler(unit0: CompilationUnit, val global: Global = new Global) {
  import global._

  private[this] val phases: Vector[Phase] = Vector(
    new Prepare(global),
    new ExpandRules(global),
    new Curry(global),
    new CleanEmbedded(global),
    new PlanRules(global)
  )

  private[this] val unit1 = if(addEraseDup) {
    val erase = globalSymbols.define("erase", isCons = true, isDef = true, returnArity = 0)
    val dup = globalSymbols.define("dup", isCons = true, isDef = true, arity = 2, returnArity = 2)
    unit0.copy(statements = Vector(DerivedRule(erase, erase), DerivedRule(erase, dup), DerivedRule(dup, dup)) ++ unit0.statements).setPos(unit0.pos)
  } else unit0

  val unit = phases.foldLeft(unit1) { case (u, p) =>
    val u2 = p(u)
    //ShowableNode.print(u2, name = s"After phase $p")
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

  def createMTInterpreter(numThreads: Int, compile: Boolean = true,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : mt.Interpreter =
    new mt.Interpreter(globalSymbols, rulePlans.values, numThreads, compile, debugBytecode, collectStats, data, initialPlans)

  def createSTInterpreter(compile: Boolean = true,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : st.Interpreter =
    new st.Interpreter(globalSymbols, rulePlans, compile, debugBytecode, collectStats, initialPlans)

  def createInterpreter(spec: String,
      debugBytecode: Boolean = false, collectStats: Boolean = false): BaseInterpreter = {
    spec match {
      case s"st.i" => createSTInterpreter(compile = false, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"st.c" => createSTInterpreter(compile = true, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"mt${mode}.i" => createMTInterpreter(mode.toInt, compile = false, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"mt${mode}.c" => createMTInterpreter(mode.toInt, compile = true, debugBytecode = debugBytecode, collectStats = collectStats)
    }
  }
}

final class RuleKey(val sym1: Symbol, val sym2: Symbol) {
  override def equals(o: Any): Boolean = o match {
    case o: RuleKey => o.sym1 == sym1 && o.sym2 == sym2 || o.sym1 == sym2 && o.sym2 == sym1
    case _ => false
  }
  override def hashCode(): Int = sym1.hashCode() + sym2.hashCode()
}

trait Phase extends (CompilationUnit => CompilationUnit) {
  override def toString(): String = getClass.getName.replaceAll(".*\\.", "")
}
