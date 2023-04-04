package de.szeiger.interact

import org.junit.Test
import org.junit.Assert._

import java.nio.file.Path

class MainTest {

  @Test
  def test1(): Unit = {
    val statements = Parser.parse(Path.of("src/test/resources/test1.in"))
    val model = new Model(statements)
    val inter = model.createInterpreter
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
    val inter = model.createInterpreter
    val steps = inter.reduce()
    assertEquals(2, steps)
  }
}
