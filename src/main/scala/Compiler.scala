package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable

class Compiler(val unit: CompilationUnit, val global: Global = new Global) {
  import global._

  val phases: Vector[Phase] = Vector(
    new Prepare(global),
    new ExpandRules(global),
    new Curry(global),
    new CheckVariables(global)
  )

  val unit1 = if(addEraseDup) {
    val erase = globalSymbols.define("erase", isCons = true, isDef = true, returnArity = 0)
    val dup = globalSymbols.define("dup", isCons = true, isDef = true, arity = 2, returnArity = 2)
    unit.copy(statements = Vector(DerivedRule(erase, erase), DerivedRule(erase, dup), DerivedRule(dup, dup)) ++ unit.statements).setPos(unit.pos)
  } else unit

  val unit2 = phases.foldLeft(unit1) { case (u, p) =>
    val u2 = p(u)
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

  def createST2Interpreter(compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : st2.Interpreter =
    new st2.Interpreter(globalSymbols, checkedRules.values, compile, debugLog, debugBytecode, collectStats)

  def createST3Interpreter(compile: Boolean = true, debugLog: Boolean = false,
    debugBytecode: Boolean = false, collectStats: Boolean = false) : st3.Interpreter =
    new st3.Interpreter(globalSymbols, checkedRules.values, compile, debugLog, debugBytecode, collectStats)

  def createInterpreter(spec: String, debugLog: Boolean = false,
      debugBytecode: Boolean = false, collectStats: Boolean = false): BaseInterpreter = {
    spec match {
      case s"st2.i" => createST2Interpreter(compile = false, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"st2.c" => createST2Interpreter(compile = true, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"st3.i" => createST3Interpreter(compile = false, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"st3.c" => createST3Interpreter(compile = true, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"mt${mode}.i" => createMTInterpreter(mode.toInt, compile = false, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
      case s"mt${mode}.c" => createMTInterpreter(mode.toInt, compile = true, debugLog = debugLog, debugBytecode = debugBytecode, collectStats = collectStats)
    }
  }

  def setDataIn(scope: Scope[_]): Unit = {
    scope.clear()
    data.foreach(scope.addData(_))
  }
}

trait Phase extends (CompilationUnit => CompilationUnit)
