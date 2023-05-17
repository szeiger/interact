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
      (_.createST2Interpreter, "st2"),
      (_.createMTInterpreter(0), "mt0"),
      (_.createMTInterpreter(1), "mt1"),
      (_.createMTInterpreter(8), "mt8"),
      (_.createMTInterpreter(1001), "mt1001"),
      (_.createMTInterpreter(1008), "mt1008"),
    ).map { case (f, s) => Array[AnyRef](f, s) }.asJava
}
