package de.szeiger.interact

import org.openjdk.jmh.annotations._
import org.openjdk.jmh.infra._

import java.nio.file.Path
import java.util.concurrent.TimeUnit

@BenchmarkMode(Array(Mode.Throughput))
@Fork(value = 1, jvmArgsAppend = Array("-Xmx12g", "-Xss32M", "-XX:+UnlockExperimentalVMOptions", "-XX:+UseZGC"))
@Threads(1)
@Warmup(iterations = 11, time = 1)
@Measurement(iterations = 11, time = 1)
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

  private val ack38Src =
    """def ack(_, y) = r
      |  | Z => S(y)
      |  | S(x) => ack_Sx(y, x)
      |def ack_Sx(_, x) = r
      |  | Z => ack(x, S(Z))
      |  | S(y) => (x1, x2) = dup(x); ack(x1, ack_Sx(y, x2))
      |let res = ack(3n, 8n)
      |""".stripMargin

  private val ack38bSrc =
    """cons Pred(x)
      |cons A(r, y) = x
      |cons A1(r, y) = x
      |match Pred(r) = Z => r = Z
      |match Pred(r) = S(x) => r = x
      |match A(a, b) = Z => a = r; b = S(r)
      |match A1(a, b) = Z => a = Pred(A(S(Z), b))
      |match A(a, b) = S(x) => a = A1(S(x), b)
      |match A1(a, b) = S(y) => (a1, a2) = dup(a); a1 = Pred(A(r1, b)); a2 = A(y, r1)
      |let A(8n, res2) = 3n
      |""".stripMargin

  class PreparedInterpreter(source: String) {
    val model: Compiler = new Compiler(Parser.parse(source), Config(spec).copy(showAfter = Set()))

    {
      val i = model.createInterpreter(model.global.config.copy(collectStats = true, logCodeGenSummary = true))
      i.initData()
      println()
      i.reduce()
      i.getMetrics.log()
      println()
    }

    val inter = model.createInterpreter()
    //val inter = model.createInterpreter(model.global.config.copy(writeOutput = Some(Path.of("gen-classes")), writeJava = Some(Path.of("gen-src"))))
    //val inter = model.createInterpreter(model.global.config.copy(skipCodeGen = true))
    def setup(): BaseInterpreter = {
      inter.initData()
      inter
    }
  }

  private lazy val mult1Inter: PreparedInterpreter = new PreparedInterpreter(prelude + mult1Src)
  private lazy val mult2Inter: PreparedInterpreter = new PreparedInterpreter(prelude + mult2Src)
  private lazy val mult3Inter: PreparedInterpreter = new PreparedInterpreter(prelude + mult3Src)
  private lazy val fib22Inter: PreparedInterpreter = new PreparedInterpreter(prelude + fib22Src)
  private lazy val fib29Inter: PreparedInterpreter = new PreparedInterpreter(prelude + fib29Src)
  private lazy val ack38Inter: PreparedInterpreter = new PreparedInterpreter(prelude + ack38Src)
  private lazy val ack38bInter: PreparedInterpreter = new PreparedInterpreter(prelude + ack38bSrc)

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
  @OperationsPerInvocation(450002)
  def fib22(bh: Blackhole): Unit =
    bh.consume(fib22Inter.setup().reduce())

//  @Benchmark
//  @OperationsPerInvocation(15670976)
//  def fib29(bh: Blackhole): Unit =
//    bh.consume(fib29Inter.setup().reduce())

  @Benchmark
  @OperationsPerInvocation(4182049)
  def ack38(bh: Blackhole): Unit =
    bh.consume(ack38Inter.setup().reduce())

  @Benchmark
  @OperationsPerInvocation(8360028)
  def ack38b(bh: Blackhole): Unit =
    bh.consume(ack38bInter.setup().reduce())
}
