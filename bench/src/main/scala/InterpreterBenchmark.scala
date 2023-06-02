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

  @Param(Array(
    //"st2.i", "st2.c",
    "st3.i",
    "st3.c",
    //"mt0.i", //"mt1.i", "mt8.i",
    //"mt1000.i", "mt1001.i", "mt1008.i",
    //"mt0.c", //"mt1.c", "mt8.c",
    //"mt1000.c", "mt1001.c", "mt1008.c",
  ))
  var spec: String = _

  private val prelude =
    """cons Z
      |cons S(n)
      |cons Add(y, r) . x
      |  cut Z = y . r
      |  cut S(x) = Add(S(y), r) . x
      |""".stripMargin

  private val mult1Src =
    """cons Mult(y, r) . x
      |  cut Z = r . Z, y . erase
      |  cut S(x) = x . Mult(a, Add(b, r)), y . dup (a, b)
      |let y = 100'c, x = 100'c, Mult(y, res) = x
      |""".stripMargin

  private val mult2Src =
    """cons Mult(y, r) . x
      |  cut Z = r . Z, y . erase
      |  cut S(x) = x . Mult(a, Add(b, r)), y . dup (a, b)
      |let
      |  y1 = 100'c, x1 = 100'c, Mult(y1, res1) = x1,
      |  y2 = 100'c, x2 = 100'c, Mult(y2, res2) = x2,
      |  y3 = 100'c, x3 = 100'c, Mult(y3, res3) = x3,
      |  y4 = 100'c, x4 = 100'c, Mult(y4, res4) = x4
      |""".stripMargin

  private val mult3Src =
    """cons Mult(y, r) . x
      |  cut Z = r . Z, y . erase
      |  cut S(x) = x . Mult(a, s1), y . dup (a, b), b . Add(s1, r)
      |let
      |  y = 1000'c,
      |  x = 1000'c,
      |  Mult(y, res) = x
      |""".stripMargin

  private val fib22Src =
    """cons Fib(res) . x
      |  cut Z = res . 1'c
      |  cut S(n) = Fib2(res) . n
      |cons Fib2(res) . x
      |  cut Z = res . 1'c
      |  cut S(n) = dup(v3, Fib(v)) . n, Fib(Add2(v, res)) . S(v3)
      |cons Add2(y, r) . x
      |  cut Z = y . r
      |  cut S(x) = r . S(v), x . Add2(y, v)
      |let
      |   22'c = Fib(res)
      |""".stripMargin

  private val fib29Src =
    """cons Fib(res) . x
      |  cut Z = res . 1'c
      |  cut S(n) = Fib2(res) . n
      |cons Fib2(res) . x
      |  cut Z = res . 1'c
      |  cut S(n) = dup(v3, Fib(v)) . n, Fib(Add2(v, res)) . S(v3)
      |cons Add2(y, r) . x
      |  cut Z = y . r
      |  cut S(x) = r . S(v), x . Add2(y, v)
      |let
      |   29'c = Fib(res)
      |""".stripMargin

  class PreparedInterpreter(source: String) {
    val model: Model = new Model(Parser.parse(source))
    val inter = model.createInterpreter(spec)
    def setup(): BaseInterpreter = {
      model.setData(inter)
      inter
    }
  }

  private var mult1Inter: PreparedInterpreter = _
  private var mult2Inter: PreparedInterpreter = _
  private var mult3Inter: PreparedInterpreter = _
  private var fib22Inter: PreparedInterpreter = _
  private var fib29Inter: PreparedInterpreter = _

  @Setup(Level.Trial)
  def init: Unit = {
    this.mult1Inter = new PreparedInterpreter(prelude + mult1Src)
    this.mult2Inter = new PreparedInterpreter(prelude + mult2Src)
    this.mult3Inter = new PreparedInterpreter(prelude + mult3Src)
    this.fib22Inter = new PreparedInterpreter(prelude + fib22Src)
    this.fib29Inter = new PreparedInterpreter(prelude + fib29Src)
  }

  @Benchmark
  def mult1(bh: Blackhole): Unit =
    bh.consume(mult1Inter.setup().reduce())

  @Benchmark
  def mult2(bh: Blackhole): Unit =
    bh.consume(mult2Inter.setup().reduce())

  @Benchmark
  def mult3(bh: Blackhole): Unit =
    bh.consume(mult3Inter.setup().reduce())

  @Benchmark
  def fib22(bh: Blackhole): Unit =
    bh.consume(fib22Inter.setup().reduce())

  @Benchmark
  def fib29(bh: Blackhole): Unit =
    bh.consume(fib29Inter.setup().reduce())

//  @Benchmark
//  def createInterpreter(bh: Blackhole): Unit = {
//    bh.consume(new PreparedInterpreter(prelude + mult1Src))
//    bh.consume(new PreparedInterpreter(prelude + mult2Src))
//    bh.consume(new PreparedInterpreter(prelude + mult3Src))
//    bh.consume(new PreparedInterpreter(prelude + fib22Src))
//    bh.consume(new PreparedInterpreter(prelude + fib29Src))
//  }
}
