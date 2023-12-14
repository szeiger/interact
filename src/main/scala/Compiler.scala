package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable

class Compiler(val unit: CompilationUnit, val global: Global = new Global) {
  import global._

  val phases: Vector[Phase] = Vector(
    new Prepare(global),
    new ExpandRules(global),
    new Curry(global),
    new CleanEmbedded(global)
  )

  val unit1 = if(addEraseDup) {
    val erase = globalSymbols.define("erase", isCons = true, isDef = true, returnArity = 0)
    val dup = globalSymbols.define("dup", isCons = true, isDef = true, arity = 2, returnArity = 2)
    unit.copy(statements = Vector(DerivedRule(erase, erase), DerivedRule(erase, dup), DerivedRule(dup, dup)) ++ unit.statements).setPos(unit.pos)
  } else unit

  val unit2 = phases.foldLeft(unit1) { case (u, p) =>
    val u2 = p(u)
    //ShowableNode.print(u2, name = s"After phase $p")
    checkThrow()
    u2
  }

  private[this] val checkedRules = mutable.Map.empty[(String, String), CheckedRule]
  private[this] val data = mutable.ArrayBuffer.empty[Let]
  unit2.statements.foreach {
    case l: Let => data += l
    case cr: CheckedRule =>
      val key = if(cr.sym1.id <= cr.sym2.id) (cr.sym1.id, cr.sym2.id) else (cr.sym2.id, cr.sym1.id)
      if(checkedRules.contains(key)) error(s"Duplicate rule ${cr.sym1} <-> ${cr.sym2}", cr)
      checkedRules.put(key, cr)
  }
  checkThrow()

  def createMTInterpreter(numThreads: Int, compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : mt.Interpreter =
    new mt.Interpreter(globalSymbols, checkedRules.values, numThreads, compile, debugLog, debugBytecode, collectStats)

  def createSTInterpreter(compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : st.Interpreter =
    new st.Interpreter(globalSymbols, checkedRules.values, compile, debugLog, debugBytecode, collectStats)

  def createInterpreter(spec: String, debugLog: Boolean = false,
      debugBytecode: Boolean = false, collectStats: Boolean = false): BaseInterpreter = {
    spec match {
      case s"st.i" => createSTInterpreter(compile = false, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"st.c" => createSTInterpreter(compile = true, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"mt${mode}.i" => createMTInterpreter(mode.toInt, compile = false, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"mt${mode}.c" => createMTInterpreter(mode.toInt, compile = true, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
    }
  }

  def setDataIn(scope: Scope[_]): Unit = {
    scope.clear()
    data.foreach(scope.addData(_))
  }
}

trait Phase extends (CompilationUnit => CompilationUnit) {
  override def toString(): String = getClass.getName.replaceAll(".*\\.", "")
}
