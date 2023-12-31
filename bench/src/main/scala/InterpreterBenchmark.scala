package de.szeiger.interact

import de.szeiger.interact.ast.ShowableNode
import org.openjdk.jmh.annotations._
import org.openjdk.jmh.infra._

import java.util.concurrent.TimeUnit

@BenchmarkMode(Array(Mode.Throughput))
@Fork(value = 1, jvmArgsAppend = Array("-Xmx12g", "-Xss32M", "-XX:+UnlockExperimentalVMOptions", "-XX:+UseZGC"))
@Threads(1)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 15, time = 1)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
class InterpreterBenchmark {

  @Param(Array(
    //"st.i",
    "st.c",
    //"mt0.i", //"mt1.i", "mt8.i",
    //"mt1000.i", "mt1001.i", "mt1008.i",
    //"mt0.c", //"mt1.c", "mt8.c",
    //"mt1000.c", "mt1001.c", "mt1008.c",
  ))
  var spec: String = _

  private val prelude =
    """cons Z
      |cons S(n)
      |def add(_, y) = r
      |  | Z => y
      |  | S(x) => add(x, S(y))
      |""".stripMargin

  private val mult1Src =
    """def mult(_, y) = r
      |  | Z => erase(y); Z
      |  | S(x) => (y1, y2) = dup(y); add(mult(x, y1), y2)
      |let res = mult(100n, 100n)
      |""".stripMargin

  private val mult2Src =
    """def mult(_, y) = r
      |  | Z => erase(y); Z
      |  | S(x) => (y1, y2) = dup(y); add(mult(x, y1), y2)
      |let res1 = mult(100n, 100n)
      |    res2 = mult(100n, 100n)
      |    res3 = mult(100n, 100n)
      |    res4 = mult(100n, 100n)
      |""".stripMargin

  private val mult3Src =
    """def mult(_, y) = r
      |  | Z => erase(y); Z
      |  | S(x) => (a, b) = dup(y); add(b, mult(x, a))
      |let res = mult(1000n, 1000n)
      |""".stripMargin

  private val fib22Src =
    """def add2(_, y) = r
      |  | Z    => y
      |  | S(x) => S(add2(x, y))
      |def fib(_) = r
      |  | Z    => 1n
      |  | S(n) => fib2(n)
      |def fib2(_) = r
      |  | Z    => 1n
      |  | S(n) => (n1, n2) = dup(n); add2(fib(S(n1)), fib(n2))
      |let res = fib(22n)
      |""".stripMargin

  private val fib29Src =
    """def add2(_, y) = r
      |  | Z    => y
      |  | S(x) => S(add2(x, y))
      |def fib(_) = r
      |  | Z    => 1n
      |  | S(n) => fib2(n)
      |def fib2(_) = r
      |  | Z    => 1n
      |  | S(n) => (n1, n2) = dup(n); add2(fib(S(n1)), fib(n2))
      |let res = fib(29n)
      |""".stripMargin

  class PreparedInterpreter(source: String) {
    val model: Compiler = new Compiler(Parser.parse(source))
    val inter = model.createInterpreter(spec, collectStats = false)
    def setup(): BaseInterpreter = {
      inter.initData()
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
    //this.fib29Inter = new PreparedInterpreter(prelude + fib29Src)
    //ShowableNode.print(mult1Inter.model.unit)
  }

  @Benchmark
  @OperationsPerInvocation(505402)
  def mult1(bh: Blackhole): Unit =
    bh.consume(mult1Inter.setup().reduce())

  @Benchmark
  @OperationsPerInvocation(2021608)
  def mult2(bh: Blackhole): Unit =
    bh.consume(mult2Inter.setup().reduce())

  @Benchmark
  @OperationsPerInvocation(2004002)
  def mult3(bh: Blackhole): Unit =
    bh.consume(mult3Inter.setup().reduce())

  @Benchmark
  @OperationsPerInvocation(478658)
  def fib22(bh: Blackhole): Unit =
    bh.consume(fib22Inter.setup().reduce())

//  @Benchmark
//  @OperationsPerInvocation(16503015)
//  def fib29(bh: Blackhole): Unit =
//    bh.consume(fib29Inter.setup().reduce())

//  @Benchmark
//  def createInterpreter(bh: Blackhole): Unit = {
//    bh.consume(new PreparedInterpreter(prelude + mult1Src))
//    bh.consume(new PreparedInterpreter(prelude + mult2Src))
//    bh.consume(new PreparedInterpreter(prelude + mult3Src))
//    bh.consume(new PreparedInterpreter(prelude + fib22Src))
//    bh.consume(new PreparedInterpreter(prelude + fib29Src))
//  }
}
