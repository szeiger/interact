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
    inter.log()
    val steps = inter.reduce()
    println(s"Irreducible after $steps reductions.")
    inter.log()
    assertEquals(128, steps)
  }
}
