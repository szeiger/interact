package de.szeiger.interact

import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameters

import scala.jdk.CollectionConverters._

@RunWith(classOf[Parameterized])
class MainTest(spec: String) {
  val SCALE = 0
  val conf = Config.defaultConfig.withSpec(spec)

  def check(testName: String, scaleFactor: Int = 1, expectedSteps: Int = -1, fail: Boolean = false, config: Config = conf): Unit =
    for(i <- 1 to (if(SCALE == 0) 1 else SCALE * scaleFactor)) TestUtils.check(testName, expectedSteps, fail, config)

  @Test def testSeqDef = check("seq-def", scaleFactor = 50, expectedSteps = 32)
  @Test def testLists = check("lists")
  @Test def testParMult = check("par-mult")
  @Test def testInlining = check("inlining", expectedSteps = if(conf.compile && conf.inlineBranching) 4 else 7)
  @Test def testFib = check("fib")
  @Test def testEmbedded = check("embedded")
  @Test def testAck = check("ack", expectedSteps = 12542077)
  @Test def testDiverging = check("diverging", fail = true)
}

object MainTest {
  @Parameters(name = "{0}")
  def interpreters = Seq(
    "st.i", "st.c",
    "mt0.i", "mt1.i", "mt8.i",
    "mt1000.i", "mt1001.i", "mt1008.i",
    "mt0.c", "mt1.c", "mt8.c",
    "mt1000.c", "mt1001.c", "mt1008.c",
  ).map(s => Array[AnyRef](s)).asJava
}
