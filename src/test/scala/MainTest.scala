package de.szeiger.interact

import org.junit.Test
import org.junit.Assert._
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameters

import java.io.{ByteArrayOutputStream, PrintStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters._

@RunWith(classOf[Parameterized])
class MainTest(newInterpreter: Model => BaseInterpreter, interpreterName: String) {
  val SCALE = 0

  def check(testName: String, scaleFactor: Int = 1, expectedSteps: Int = -1): Unit = {
    val basePath = s"src/test/resources/$testName"
    for(i <- 1 to (if(SCALE == 0) 1 else SCALE * scaleFactor)) {
      //if(i % scaleFactor == 0) println(i)
      val statements = Parser.parse(Path.of(basePath+".in"))
      val model = new Model(statements)
      val inter = newInterpreter(model)
      model.setData(inter)
      val steps = inter.reduce()
      val out = new ByteArrayOutputStream()
      inter.scope.log(new PrintStream(out, true, StandardCharsets.UTF_8))
      val s = out.toString(StandardCharsets.UTF_8)
      val checkFile = Path.of(basePath+".check")
      if(Files.exists(checkFile)) {
        val check = Files.readString(checkFile, StandardCharsets.UTF_8)
        assertEquals(check.trim, s.trim)
      }
      if(expectedSteps >= 0) assertEquals(expectedSteps, steps)
    }
  }

  @Test def testSeq = check("seq", scaleFactor = 50, expectedSteps = 128)
  @Test def testParMult = check("par-mult")
  @Test def testReduceRHS = check("reduce-rhs", expectedSteps = 2)
  @Test def testFib = check("fib")
}

object MainTest {
  @Parameters(name = "{1}")
  def interpreters =
    Seq[(Model => BaseInterpreter, String)](
      (_.createST2Interpreter(compile = false, collectStats = true), "st2.i"),
      (_.createST2Interpreter(compile = true, collectStats = true, debugLog = false, debugBytecode = false), "st2.c"),
      (_.createMTInterpreter(0, compile = false, collectStats = true), "mt0.i"),
      (_.createMTInterpreter(1, compile = false, collectStats = true), "mt1.i"),
      (_.createMTInterpreter(8, compile = false, collectStats = true), "mt8.i"),
      (_.createMTInterpreter(1001, compile = false, collectStats = true), "mt1001.i"),
      (_.createMTInterpreter(1008, compile = false, collectStats = true), "mt1008.i"),
      (_.createMTInterpreter(0, compile = true, collectStats = true), "mt0.c"),
      (_.createMTInterpreter(1, compile = true, collectStats = true), "mt1.c"),
      (_.createMTInterpreter(8, compile = true, collectStats = true), "mt8.c"),
      (_.createMTInterpreter(1001, compile = true, collectStats = true), "mt1001.c"),
      (_.createMTInterpreter(1008, compile = true, collectStats = true), "mt1008.c"),
    ).map { case (f, s) => Array[AnyRef](f, s) }.asJava
}
