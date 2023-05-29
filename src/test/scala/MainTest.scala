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
class MainTest(spec: String) {
  val SCALE = 0

  def check(testName: String, scaleFactor: Int = 1, expectedSteps: Int = -1): Unit = {
    val basePath = s"src/test/resources/$testName"
    for(i <- 1 to (if(SCALE == 0) 1 else SCALE * scaleFactor)) {
      //if(i % scaleFactor == 0) println(i)
      val statements = Parser.parse(Path.of(basePath+".in"))
      val model = new Model(statements)
      val inter = model.createInterpreter(spec, collectStats = true, debugLog = false, debugBytecode = false)
      model.setData(inter)
      val steps = inter.reduce()
      val out = new ByteArrayOutputStream()
      inter.scope.log(new PrintStream(out, true, StandardCharsets.UTF_8))
      val s = out.toString(StandardCharsets.UTF_8)
      val checkFile = Path.of(basePath+".check")
      if(Files.exists(checkFile)) {
        val check = Files.readString(checkFile, StandardCharsets.UTF_8)
        //println("---- Expected ----")
        //println(check.trim)
        //println("---- Actual ----")
        //println(s.trim)
        //println("---- End ----")
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
  @Parameters(name = "{0}")
  def interpreters = Seq(
    "st2.i", "st2.c",
    "st3.i", "st3.c",
    "mt0.i", "mt1.i", "mt8.i",
    "mt1000.i", "mt1001.i", "mt1008.i",
    "mt0.c", "mt1.c", "mt8.c",
    "mt1000.c", "mt1001.c", "mt1008.c",
  ).map(s => Array[AnyRef](s)).asJava
}
