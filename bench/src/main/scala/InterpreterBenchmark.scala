package de.szeiger.interact

import org.openjdk.jmh.annotations._
import org.openjdk.jmh.infra._

import java.util.concurrent.TimeUnit

@BenchmarkMode(Array(Mode.AverageTime))
@Fork(1)
@Threads(1)
@Warmup(iterations = 10)
@Measurement(iterations = 10)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
class InterpreterBenchmark {

  private val prelude =
    """cons Z deriving Erase, Dup
      |cons S(n) deriving Erase, Dup
      |cons Erase                   deriving Erase
      |cons Dup(a, b) . in          deriving Erase
      |  cut Dup(c, d) = a . c, b . d
      |""".stripMargin

  private var multModel: Model = _

  @Setup(Level.Trial)
  def init: Unit = {
    this.multModel = new Model(Parser.parse(prelude +
      """cons Add(y, r) . x           deriving Erase, Dup
        |  cut Z = y . r
        |  cut S(x) = Add(S(y), r) . x
        |cons Mult(y, r) . x          deriving Erase, Dup
        |  cut Z = r . Z, y . Erase
        |  cut S(x) = x . Mult(a, Add(b, r)), y . Dup (a, b)
        |let res =
        |  y . 100'c,
        |  x . 100'c,
        |  Mult(y, res) . x
        |""".stripMargin))
  }

  @Benchmark
  def multMT(bh: Blackhole): Unit =
    bh.consume(multModel.createMTInterpreter.reduce())

  @Benchmark
  def multST(bh: Blackhole): Unit =
    bh.consume(multModel.createSTInterpreter.reduce())
}
