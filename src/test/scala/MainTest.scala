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

  def checkFile(basePath: String): Int = {
    val statements = Parser.parse(Path.of(basePath+".in"))
    val model = new Model(statements)
    val inter = newInterpreter(model)
    val steps = inter.reduce()
    val out = new ByteArrayOutputStream()
    inter.log(new PrintStream(out, true, StandardCharsets.UTF_8))
    val s = out.toString(StandardCharsets.UTF_8)
    val check = Files.readString(Path.of(basePath+".check"), StandardCharsets.UTF_8)
    assertEquals(check.trim, s.trim)
    steps
  }

  @Test
  def test1(): Unit = for(i <- 1 to (if(SCALE == 0) 1 else SCALE * 50)) {
    if(i % 10 == 0) println(i)
    val steps = checkFile("src/test/resources/test1")
    // mt is non-deterministic due to extra boundary cells
    if(interpreterName == "st") assertEquals(128, steps)
  }

  @Test
  def test2(): Unit = for(i <- 1 to (if(SCALE == 0) 1 else SCALE)) {
    println(i)
    checkFile("src/test/resources/test2")
  }

  @Test
  def testReduceRHS(): Unit = {
    val statements = Parser.parse(
      """cons A(x)
        |cons B
        |cons C(x)
        |cons D
        |rule A(x) . B = C(x) . D, A(D) . C(D)
        |rule C(x) . D = x . D
        |let res = A(res) . B
        |""".stripMargin)
    val model = new Model(statements)
    val inter = newInterpreter(model)
    val steps = inter.reduce()
    assertEquals(2, steps)
  }
}

object MainTest {
  @Parameters(name = "{1}")
  def interpreters =
    Seq[(Model => BaseInterpreter, String)](
      (_.createSTInterpreter, "st"),
      (_.createMTInterpreter(0), "mt0"),
      (_.createMTInterpreter(1), "mt1"),
      (_.createMTInterpreter(8), "mt8"),
      (_.createMTInterpreter(1001), "mt1001"),
      (_.createMTInterpreter(1008), "mt1008"),
    ).map { case (f, s) => Array[AnyRef](f, s) }.asJava
}
