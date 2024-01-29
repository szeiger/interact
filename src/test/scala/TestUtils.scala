package de.szeiger.interact

import org.junit.Assert
import org.junit.Assert._

import java.io.{ByteArrayOutputStream, PrintStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import java.util.concurrent.atomic.AtomicInteger

object TestUtils {
  def check(testName: String, spec: String, expectedSteps: Int = -1, addEraseDup: Boolean = true, fail: Boolean = false): Unit = {
    val basePath = s"src/test/resources/$testName"
    val statements = Parser.parse(Path.of(basePath+".in"))
    val (result, success, steps) = try {
      val model = new Compiler(statements, Config(spec).copy(addEraseDup = addEraseDup, showAfter = Set()))
      val inter = model.createInterpreter(model.global.config.copy(collectStats = true))
      inter.initData()
      inter.reduce()
      if(inter.getMetrics != null) inter.getMetrics.logStats()
      val out = new ByteArrayOutputStream()
      inter.getAnalyzer.log(new PrintStream(out, true, StandardCharsets.UTF_8), color = false)
      (out.toString(StandardCharsets.UTF_8), true, inter.getMetrics.getSteps)
    } catch {
      case ex: CompilerResult => (Colors.stripColors(ex.getMessage).replace("src\\test\\resources\\", "src/test/resources/"), false, -1)
    }
    val checkFile = Path.of(basePath+".check")
    if(Files.exists(checkFile)) {
      val check = Files.readString(checkFile, StandardCharsets.UTF_8)
      if(check.trim.replaceAll("\r", "") != result.trim.replaceAll("\r", "")) {
        println("---- Expected ----")
        println(check)
        println("---- Actual ----")
        println(result)
        println("---- End ----")
        assertEquals(check.trim.replaceAll("\r", ""), result.trim.replaceAll("\r", ""))
      }
    }
    if(fail && success) Assert.fail("Failure expected")
    else if(!fail && !success) Assert.fail("Unexpected failure")
    if(expectedSteps >= 0 && success) assertEquals(s"Expected $expectedSteps steps, but fully reduced after $steps", expectedSteps, steps)
  }
}

class ManagedDummy(name: String) extends LifecycleManaged {
  private[this] val copied, erased = new AtomicInteger()
  override def toString: String = s"$name:$copied:$erased"
  override def erase(): Unit = erased.incrementAndGet()
  override def copy(): LifecycleManaged = { copied.incrementAndGet(); this }
}
object ManagedDummy {
  def create(name: String, res: RefOutput): Unit = res.setValue(new ManagedDummy(name))
}
