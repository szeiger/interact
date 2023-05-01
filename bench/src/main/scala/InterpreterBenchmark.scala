package de.szeiger.interact

import org.openjdk.jmh.annotations._
import org.openjdk.jmh.infra._

import java.util.concurrent.TimeUnit

@BenchmarkMode(Array(Mode.AverageTime))
@Fork(value = 1, jvmArgsAppend = Array("-Xmx16g", "-XX:+UnlockExperimentalVMOptions", "-XX:+UseZGC"))
@Threads(1)
@Warmup(iterations = 20)
@Measurement(iterations = 20)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
class InterpreterBenchmark {

  @Param(Array("-1", "0", "1", "4", "1001", "1004"))
  //@Param(Array("1", "4"))
  //@Param(Array("0"))
  private var mode: Int = _

  private val prelude =
    """cons Z deriving Erase, Dup
      |cons S(n) deriving Erase, Dup
      |cons Erase                   deriving Erase
      |cons Dup(a, b) . in          deriving Erase
      |  cut Dup(c, d) = a . c, b . d
      |cons Add(y, r) . x           deriving Erase, Dup
      |  cut Z = y . r
      |  cut S(x) = Add(S(y), r) . x
      |""".stripMargin

  private var multModel1: Model = _
  private var multModel2: Model = _
  private var multModel3: Model = _

  @Setup(Level.Trial)
  def init: Unit = {
    this.multModel1 = new Model(Parser.parse(prelude +
      """cons Mult(y, r) . x          deriving Erase, Dup
        |  cut Z = r . Z, y . Erase
        |  cut S(x) = x . Mult(a, Add(b, r)), y . Dup (a, b)
        |let res =
        |  y . 100'c, x . 100'c, Mult(y, res) . x
        |""".stripMargin))
    this.multModel2 = new Model(Parser.parse(prelude +
      """cons Mult(y, r) . x          deriving Erase, Dup
        |  cut Z = r . Z, y . Erase
        |  cut S(x) = x . Mult(a, Add(b, r)), y . Dup (a, b)
        |let res1, res2, res3, res4 =
        |  y1 . 100'c, x1 . 100'c, Mult(y1, res1) . x1,
        |  y2 . 100'c, x2 . 100'c, Mult(y2, res2) . x2,
        |  y3 . 100'c, x3 . 100'c, Mult(y3, res3) . x3,
        |  y4 . 100'c, x4 . 100'c, Mult(y4, res4) . x4
        |""".stripMargin))
    this.multModel3 = new Model(Parser.parse(prelude +
      """cons Mult(y, r) . x          deriving Erase, Dup
        |  cut Z = r . Z, y . Erase
        |  cut S(x) = x . Mult(a, s1), y . Dup (a, b), b . Add(s1, r)
        |let res =
        |  y . 1000'c,
        |  x . 1000'c,
        |  Mult(y, res) . x
        |""".stripMargin))
  }

  def getInterpreter(m: Model): BaseInterpreter =
    if(mode == -1) m.createSTInterpreter
    else m.createMTInterpreter(mode)

  @Benchmark
  def mult1(bh: Blackhole): Unit =
    bh.consume(getInterpreter(multModel1).reduce())

  @Benchmark
  def mult2(bh: Blackhole): Unit =
    bh.consume(getInterpreter(multModel2).reduce())

  @Benchmark
  def mult3(bh: Blackhole): Unit =
    bh.consume(getInterpreter(multModel3).reduce())

//  @Benchmark
//  def createInterpreter(bh: Blackhole): Unit = {
//    bh.consume(getInterpreter(multModel1))
//    bh.consume(getInterpreter(multModel2))
//    bh.consume(getInterpreter(multModel3))
//  }
}
