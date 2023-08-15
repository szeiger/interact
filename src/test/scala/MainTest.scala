package de.szeiger.interact

import org.junit.Test
import org.junit.Assert._
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameters

import java.util.concurrent.atomic.AtomicInteger
import scala.jdk.CollectionConverters._

@RunWith(classOf[Parameterized])
class MainTest(spec: String) {
  val SCALE = 0

  def check(testName: String, scaleFactor: Int = 1, expectedSteps: Int = -1, addEraseDup: Boolean = true): Unit =
    for(i <- 1 to (if(SCALE == 0) 1 else SCALE * scaleFactor)) TestUtils.check(testName, spec, expectedSteps, addEraseDup)

  @Test def testSeqDef = check("seq-def", scaleFactor = 50, expectedSteps = 32)
  @Test def testLists = check("lists")
  @Test def testParMult = check("par-mult")
  @Test def testReduceRHS = check("reduce-rhs", expectedSteps = 2, addEraseDup = false)
  @Test def testFib = check("fib")
  @Test def testEmbedded = check("embedded")

  @Test def testLifecycle = {

  }
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
