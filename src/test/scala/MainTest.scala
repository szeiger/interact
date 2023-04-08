package de.szeiger.interact

import org.junit.Test
import org.junit.Assert._
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameters

import java.nio.file.Path
import scala.jdk.CollectionConverters._

@RunWith(classOf[Parameterized])
class MainTest(newInterpreter: Model => BaseInterpreter, interpreterName: String) {

  @Test
  def test1(): Unit = {
    val statements = Parser.parse(Path.of("src/test/resources/test1.in"))
    val model = new Model(statements)
    val inter = newInterpreter(model)
    //inter.log()
    val steps = inter.reduce()
    //println(s"Irreducible after $steps reductions.")
    //inter.log()
    assertEquals(128, steps)
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
      (_.createMTInterpreter, "mt")
    ).map { case (f, s) => Array[AnyRef](f, s) }.asJava
}
