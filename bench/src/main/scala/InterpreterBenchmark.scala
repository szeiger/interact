package de.szeiger.interact

import org.openjdk.jmh.annotations._
import org.openjdk.jmh.infra._
import org.openjdk.jmh.runner.{Defaults, Runner}
import org.openjdk.jmh.runner.format.OutputFormatFactory
import org.openjdk.jmh.runner.options.CommandLineOptions
import org.openjdk.jmh.util.Optional

import java.nio.file.Path
import scala.jdk.CollectionConverters._
import java.util.concurrent.TimeUnit
import scala.util.control.NonFatal

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
    "stc1",
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
    "intAck38",
    "boxedAck38",
    "fib22",
    "mult1",
    "mult2",
    "mult3",
    "intMult3",
    "intFib29",
//    "fib29",
  ))
  var benchmark: String = _

  private[this] var inter: BaseInterpreter = _

  @Setup(Level.Trial)
  def setup(): Unit = inter = InterpreterBenchmark.setup(spec, benchmark)

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

  private val mult1Src = prelude +
    """def mult(_, y) = r
      |  | Z => erase(y); Z
      |  | S(x) => (y1, y2) = dup(y); add(mult(x, y1), y2)
      |let res = mult(100n, 100n)
      |""".stripMargin

  private val mult2Src = prelude +
    """def mult(_, y) = r
      |  | Z => erase(y); Z
      |  | S(x) => (y1, y2) = dup(y); add(mult(x, y1), y2)
      |let res1 = mult(100n, 100n)
      |    res2 = mult(100n, 100n)
      |    res3 = mult(100n, 100n)
      |    res4 = mult(100n, 100n)
      |""".stripMargin

  private val mult3Src = prelude +
    """def mult(_, y) = r
      |  | Z => erase(y); Z
      |  | S(x) => (a, b) = dup(y); add(b, mult(x, a))
      |let res = mult(1000n, 1000n)
      |""".stripMargin

  private val intMult3Src =
    """cons Int[int]
      |def add(_, _) = r
      |  | Int[x], Int[y] if [x == 0] => Int[y]
      |                   else        => add(Int[x-1], Int[y+1])
      |def mult(_, _) = r
      |  | Int[x], Int[y] if [x == 0] => Int[0]
      |                   else        => add(Int[y], mult(Int[x-1], Int[y]))
      |let res = mult(Int[1000], Int[1000])
      |""".stripMargin

  private val fib22Src = prelude +
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

  private val fib29Src = prelude +
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

  private val intFib29Src =
    """cons Int[int]
      |def _ + _ = r
      |  | Int[x], Int[y] => Int[x + y]
      |def fib(_) = r
      | | Int[x] if [x == 0] => Int[1]
      |          if [x == 1] => Int[1]
      |          else        => fib(Int[x-1]) + fib(Int[x-2])
      |let res = fib(Int[29])
      |""".stripMargin

  private val ack38Src = prelude +
    """def ack(_, y) = r
      |  | Z => S(y)
      |  | S(x) => ack_Sx(y, x)
      |def ack_Sx(_, x) = r
      |  | Z => ack(x, S(Z))
      |  | S(y) => (x1, x2) = dup(x); ack(x1, ack_Sx(y, x2))
      |let res = ack(3n, 8n)
      |""".stripMargin

  private val ack38bSrc = prelude +
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

  private val intAck38Src =
    """cons Int[int]
      |
      |def ackU(a, b) = r
      |  | Int[x], Int[y]
      |      if [x == 0] => Int[y + 1]
      |      if [y == 0] => ackU(Int[x - 1], Int[1])
      |      else        => ackU(Int[x - 1], ackU(Int[x], Int[y - 1]))
      |
      |let resU = ackU(Int[3], Int[8])
      |""".stripMargin

  private val boxedAck38Src =
    """cons BoxedInt[ref]
      |
      |def ackB(a, b) = r
      |  | BoxedInt[x], BoxedInt[y]
      |      if [de.szeiger.interact.InterpreterBenchmark.is0(x)] =>
      |        BoxedInt[de.szeiger.interact.InterpreterBenchmark.inc(y)]
      |        [eraseRef(x)]
      |      if [de.szeiger.interact.InterpreterBenchmark.is0(y)] =>
      |        ackB(BoxedInt[de.szeiger.interact.InterpreterBenchmark.dec(x)], BoxedInt[de.szeiger.interact.InterpreterBenchmark.box(1)])
      |        [eraseRef(y)]
      |      else =>
      |        [de.szeiger.interact.InterpreterBenchmark.ackHelper(x, x1, x2)]
      |        ackB(BoxedInt[x1], ackB(BoxedInt[x2], BoxedInt[de.szeiger.interact.InterpreterBenchmark.dec(y)]))
      |
      |let resB = ackB(BoxedInt[de.szeiger.interact.InterpreterBenchmark.box(3)], BoxedInt[de.szeiger.interact.InterpreterBenchmark.box(8)])
      |""".stripMargin
  def is0(i: java.lang.Integer): Boolean = i.intValue() == 0
  def box(i: Int): java.lang.Integer = Integer.valueOf(i)
  def inc(i: java.lang.Integer): java.lang.Integer = box(i.intValue() + 1)
  def dec(i: java.lang.Integer): java.lang.Integer = box(i.intValue() - 1)
  def ackHelper(i: java.lang.Integer, o1: RefOutput, o2: RefOutput): Unit = {
    o1.setValue(dec(i))
    o2.setValue(i)
  }

  val testCases = Map(
    "ack38" -> ack38Src,
    "ack38b" -> ack38bSrc,
    "boxedAck38" -> boxedAck38Src,
    "intAck38" -> intAck38Src,
    "fib22" -> fib22Src,
    "intFib29" -> intFib29Src,
    "fib29" -> fib29Src,
    "mult1" -> mult1Src,
    "mult2" -> mult2Src,
    "mult3" -> mult3Src,
    "intMult3" -> intMult3Src,
  )

  val prepareConfig: Config => Config =
    _.copy(collectStats = true, logCodeGenSummary = true, showAfter = Set("PlanRules"))

  val benchConfig: Config => Config =
    //identity
    _.copy(writeOutput = Some(Path.of("gen-classes")), writeJava = Some(Path.of("gen-src")), logGeneratedClasses = None, showAfter = Set(""))
    //_.copy(skipCodeGen = Set(""))

  def setup(spec: String, benchmark: String): BaseInterpreter =
    new Compiler(Parser.parse(testCases(benchmark)), benchConfig(Config(spec))).createInterpreter()

  def main(args: Array[String]): Unit = {
    val cls = classOf[InterpreterBenchmark]

    def run1(testCase: String, spec: String) = {
      try {
        println(s"-------------------- Running $testCase $spec:")
        val i = new Compiler(Parser.parse(testCases(testCase)), prepareConfig(Config(spec))).createInterpreter()
        i.initData()
        println()
        i.reduce()
        val m = i.getMetrics
        m.log()
        val steps = m.getSteps
        i.dispose()
        println()
        val opts = new CommandLineOptions(cls.getName, s"-pbenchmark=$testCase", s"-pspec=$spec") {
          override def getOperationsPerInvocation = Optional.of(steps)
        }
        val runner = new Runner(opts)
        runner.run().asScala
      } catch { case NonFatal(ex) =>
        ex.printStackTrace()
        Iterable.empty
      }
    }

    val res = for {
      testCase <- cls.getDeclaredField("benchmark").getAnnotation(classOf[Param]).value().toVector
      spec <- cls.getDeclaredField("spec").getAnnotation(classOf[Param]).value()
      res <- run1(testCase, spec)
    } yield res

    println("-------------------- Results")
    System.out.flush()
    val out = OutputFormatFactory.createFormatInstance(System.out, Defaults.VERBOSITY)
    out.endRun(res.asJava)
  }
}
