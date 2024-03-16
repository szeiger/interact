package de.szeiger.interact

import org.openjdk.jmh.annotations._
import org.openjdk.jmh.infra._
import org.openjdk.jmh.runner.{Defaults, Runner}
import org.openjdk.jmh.runner.format.OutputFormatFactory
import org.openjdk.jmh.runner.options.CommandLineOptions
import org.openjdk.jmh.util.Optional

import scala.jdk.CollectionConverters._
import java.util.concurrent.TimeUnit

// bench/jmh:runMain de.szeiger.interact.InterpreterBenchmark

@BenchmarkMode(Array(Mode.Throughput))
@Fork(value = 1, jvmArgsAppend = Array("-Xmx12g", "-Xss32M", "-XX:+UnlockExperimentalVMOptions", "-XX:+UseZGC",
  "-XX:+UnlockDiagnosticVMOptions"))
@Threads(1)
@Warmup(iterations = 11, time = 1)
@Measurement(iterations = 11, time = 1)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
class InterpreterBenchmark {

  @Param(Array(
    //"sti",
    //"stc1",
    "stc2",
    //"mt0.i", //"mt1.i", "mt8.i",
    //"mt1000.i", "mt1001.i", "mt1008.i",
    //"mt0.c", //"mt1.c", "mt8.c",
    //"mt1000.c", "mt1001.c", "mt1008.c",
  ))
  var spec: String = _

  @Param(Array(
    "ack38",
    "ack38b",
    "fib22",
    "mult1",
    "mult2",
    "mult3",
    //"fib29",
  ))
  var benchmark: String = _

  private[this] var inter: BaseInterpreter = _

  @Setup(Level.Trial)
  def setup(): Unit = {
    val config = Config(spec).copy(showAfter = Set(""))
    val prepareConfig = config.copy(collectStats = true, logCodeGenSummary = true)
    val benchConfig = config
    //val benchConfig = config.copy(writeOutput = Some(Path.of("gen-classes")), writeJava = Some(Path.of("gen-src")), logGeneratedClasses = None, showAfter = Set(""))
    //val benchConfig = config.copy(skipCodeGen = true)
    val (source, expectedSteps) = InterpreterBenchmark.testCases(benchmark)
    val i = new Compiler(Parser.parse(source), prepareConfig).createInterpreter()
    i.initData()
    println()
    i.reduce()
    val m = i.getMetrics
    m.log()
    assert(m.getSteps == expectedSteps)
    i.dispose()
    println()
    inter = new Compiler(Parser.parse(source), benchConfig).createInterpreter()
  }

  @Setup(Level.Invocation)
  def prepare(): Unit = inter.initData()

  @Benchmark
  def run(bh: Blackhole): Unit = bh.consume(inter.reduce())

  @TearDown(Level.Invocation)
  def cleanup(): Unit = inter.dispose()
}

object InterpreterBenchmark {
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

  val testCases = Map(
    "ack38" -> (prelude + ack38Src, 4182049),
    "ack38b" -> (prelude + ack38bSrc, 8360028),
    "fib22" -> (prelude + fib22Src, 450002),
    "fib29" -> (prelude + fib29Src, 15670976),
    "mult1" -> (prelude + mult1Src, 505402),
    "mult2" -> (prelude + mult2Src, 2021608),
    "mult3" -> (prelude + mult3Src, 2004002),
  )

  def main(args: Array[String]): Unit = {
    val cls = classOf[InterpreterBenchmark]

    def run1(testCase: String, spec: String) = {
      println(s"-------------------- Running $testCase $spec:")
      val opts = new CommandLineOptions(cls.getName, s"-pbenchmark=$testCase", s"-pspec=$spec") {
        override def getOperationsPerInvocation = Optional.of(testCases(testCase)._2)
      }
      val runner = new Runner(opts)
      runner.run()
    }

    val res = for {
      testCase <- cls.getDeclaredField("benchmark").getAnnotation(classOf[Param]).value().toVector
      spec <- cls.getDeclaredField("spec").getAnnotation(classOf[Param]).value()
      res <- run1(testCase, spec).asScala
    } yield res

    println("-------------------- Results")
    System.out.flush()
    val out = OutputFormatFactory.createFormatInstance(System.out, Defaults.VERBOSITY)
    out.endRun(res.asJava)
  }
}
