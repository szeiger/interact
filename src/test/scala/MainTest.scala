package de.szeiger.interact

import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameters

import java.nio.file.Path
import scala.jdk.CollectionConverters._

@RunWith(classOf[Parameterized])
class MainTest(spec: String) {
  val SCALE = 0
  val conf = Config.defaultConfig.withSpec(spec).copy(showAfter = Set(""), phaseLog = Set(""),
    //writeOutput = Some(Path.of("bench/gen-classes")), writeJava = Some(Path.of("bench/gen-src"))
  )

  def check(testName: String, scaleFactor: Int = 1, expectedSteps: Int = -1, fail: Boolean = false, config: Config = conf): Unit =
    for(i <- 1 to (if(SCALE == 0) 1 else SCALE * scaleFactor)) TestUtils.check(testName, expectedSteps, fail, config)

  @Test def testSeqDef = check("seq-def", scaleFactor = 50, expectedSteps = 32)
  @Test def testLists = check("lists")
  @Test def testParMult = check("par-mult")
  @Test def testInlining = check("inlining", expectedSteps = if(conf.backend.allowPayloadTemp) 99 else 102)
  @Test def testFib = check("fib")
  @Test def testEmbedded = check("embedded")
  @Test def testAck = check("ack", expectedSteps = if(conf.backend.allowPayloadTemp) 18114077 else 23686073)
  @Test def testDiverging = check("diverging", fail = true)
}

object MainTest {
  @Parameters(name = "{0}")
  def interpreters = Seq(
    "sti", "stc1", "stc2",
    //"mt0.i", "mt1.i", "mt8.i",
    //"mt1000.i", "mt1001.i", "mt1008.i",
    //"mt0.c", "mt1.c", "mt8.c",
    //"mt1000.c", "mt1001.c", "mt1008.c",
  ).map(s => Array[AnyRef](s)).asJava

  // used by ack.in:
  def is0(i: java.lang.Integer): Boolean = i.intValue() == 0
  def box(i: Int): java.lang.Integer = Integer.valueOf(i)
  def inc(i: java.lang.Integer): java.lang.Integer = box(i.intValue() + 1)
  def dec(i: java.lang.Integer): java.lang.Integer = box(i.intValue() - 1)
  def ackHelper(i: java.lang.Integer, o1: RefOutput, o2: RefOutput): Unit = {
    o1.setValue(dec(i))
    o2.setValue(i)
  }
}
