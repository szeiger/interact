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
    //"st3.i",
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
      |def add(_, y): r
      |  | Z => y
      |  | S(x) => add(x, S(y))
      |""".stripMargin

  private val mult1Src =
    """def mult(_, y): r
      |  | Z => erase(y), Z
      |  | S(x) => (y1, y2) = dup(y), add(mult(x, y1), y2)
      |let res = mult(100'c, 100'c)
      |""".stripMargin

  private val mult2Src =
    """def mult(_, y): r
      |  | Z => erase(y), Z
      |  | S(x) => (y1, y2) = dup(y), add(mult(x, y1), y2)
      |let res1 = mult(100'c, 100'c),
      |    res2 = mult(100'c, 100'c),
      |    res3 = mult(100'c, 100'c),
      |    res4 = mult(100'c, 100'c)
      |""".stripMargin

  private val mult3Src =
    """def mult(_, y): r
      |  | Z => erase(y), Z
      |  | S(x) => (a, b) = dup(y), add(b, mult(x, a))
      |let res = mult(1000'c, 1000'c)
      |""".stripMargin

  private val fib22Src =
    """def add2(_, y): r
      |  | Z    => y
      |  | S(x) => S(add2(x, y))
      |def fib(_): r
      |  | Z    => 1'c
      |  | S(n) => fib2(n)
      |def fib2(_): r
      |  | Z    => 1'c
      |  | S(n) => (n1, n2) = dup(n), add2(fib(S(n1)), fib(n2))
      |let res = fib(22'c)
      |""".stripMargin

  private val fib29Src =
    """def add2(_, y): r
      |  | Z    => y
      |  | S(x) => S(add2(x, y))
      |def fib(_): r
      |  | Z    => 1'c
      |  | S(n) => fib2(n)
      |def fib2(_): r
      |  | Z    => 1'c
      |  | S(n) => (n1, n2) = dup(n), add2(fib(S(n1)), fib(n2))
      |let res = fib(29'c)
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
