package de.szeiger.interact

import org.junit.Assert._

import java.io.{ByteArrayOutputStream, PrintStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import java.util.concurrent.atomic.AtomicInteger

object TestUtils {
  val SCALE = 0

  def check(testName: String, spec: String, expectedSteps: Int = -1, addEraseDup: Boolean = true): Unit = {
    val basePath = s"src/test/resources/$testName"
    val statements = Parser.parse(Path.of(basePath+".in"))
    val global = new Global(addEraseDup = addEraseDup)
    val model = new Compiler(statements, global)
    val inter = model.createInterpreter(spec, collectStats = true, debugLog = false, debugBytecode = false)
    model.setDataIn(inter.scope)
    val steps = inter.reduce()
    val out = new ByteArrayOutputStream()
    inter.scope.log(new PrintStream(out, true, StandardCharsets.UTF_8), color = false)
    val s = out.toString(StandardCharsets.UTF_8)
    val checkFile = Path.of(basePath+".check")
    if(Files.exists(checkFile)) {
      val check = Files.readString(checkFile, StandardCharsets.UTF_8)
      //println("---- Expected ----")
      //println(check.trim)
      //println("---- Actual ----")
      //println(s.trim)
      //println("---- End ----")
      assertEquals(check.trim.replaceAll("\r", ""), s.trim.replaceAll("\r", ""))
    }
    if(expectedSteps >= 0) assertEquals(expectedSteps, steps)
  }
}

class ManagedDummy(name: String) extends LifecycleManaged {
  private[this] val copied, erased = new AtomicInteger()
  override def toString: String = s"$name:$copied:$erased"
  override def erase(): Unit = erased.incrementAndGet()
  override def copy(): LifecycleManaged = { copied.incrementAndGet(); this }
}
object ManagedDummy {
  def create(name: String, res: RefBox): Unit = res.setValue(new ManagedDummy(name))
}
