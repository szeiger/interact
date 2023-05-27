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

  //@Param(Array("0", "1", "4", "1001", "1004"))
  //@Param(Array("-2", "0", "1", "2", "4", "1001", "1002", "1004"))
  //@Param(Array("1", "2", "4"))
  //@Param(Array("1001", "1004"))
  @Param(Array("-3"))
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

  class PreparedInterpreter(source: String) {
    val model: Model = new Model(Parser.parse(source))
    val inter = getInterpreter(model)
    def setup(): BaseInterpreter = {
      model.setData(inter)
      inter
    }
  }
  private var mult1Inter: PreparedInterpreter = _
  private var mult2Inter: PreparedInterpreter = _
  private var mult3Inter: PreparedInterpreter = _
  private var fib22Inter: PreparedInterpreter = _

  @Setup(Level.Trial)
  def init: Unit = {
    this.mult1Inter = new PreparedInterpreter(prelude +
      """cons Mult(y, r) . x          deriving Erase, Dup
        |  cut Z = r . Z, y . Erase
        |  cut S(x) = x . Mult(a, Add(b, r)), y . Dup (a, b)
        |let res =
        |  y . 100'c, x . 100'c, Mult(y, res) . x
        |""".stripMargin)
    this.mult2Inter = new PreparedInterpreter(prelude +
      """cons Mult(y, r) . x          deriving Erase, Dup
        |  cut Z = r . Z, y . Erase
        |  cut S(x) = x . Mult(a, Add(b, r)), y . Dup (a, b)
        |let res1, res2, res3, res4 =
        |  y1 . 100'c, x1 . 100'c, Mult(y1, res1) . x1,
        |  y2 . 100'c, x2 . 100'c, Mult(y2, res2) . x2,
        |  y3 . 100'c, x3 . 100'c, Mult(y3, res3) . x3,
        |  y4 . 100'c, x4 . 100'c, Mult(y4, res4) . x4
        |""".stripMargin)
    this.mult3Inter = new PreparedInterpreter(prelude +
      """cons Mult(y, r) . x          deriving Erase, Dup
        |  cut Z = r . Z, y . Erase
        |  cut S(x) = x . Mult(a, s1), y . Dup (a, b), b . Add(s1, r)
        |let res =
        |  y . 1000'c,
        |  x . 1000'c,
        |  Mult(y, res) . x
        |""".stripMargin)
    this.fib22Inter = new PreparedInterpreter(prelude +
      """cons Fib(res) . x deriving Erase, Dup
        |  cut Z = res . 1'c
        |  cut S(n) = Fib2(res) . n
        |cons Fib2(res) . x deriving Erase, Dup
        |  cut Z = res . 1'c
        |  cut S(n) = Dup(v3, Fib(v)) . n, Fib(Add2(v, res)) . S(v3)
        |cons Add2(y, r) . x deriving Erase, Dup
        |  cut Z = y . r
        |  cut S(x) = r . S(v), x . Add2(y, v)
        |let res =
        |   22'c . Fib(res)
        |""".stripMargin)
  }

  def getInterpreter(m: Model): BaseInterpreter =
    if(mode == -2) m.createST2Interpreter(true)
    else if(mode == -3) m.createST3Interpreter(true)
    else m.createMTInterpreter(mode, true)

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

//  @Benchmark
//  def createInterpreter(bh: Blackhole): Unit = {
//    bh.consume(getInterpreter(multModel1))
//    bh.consume(getInterpreter(multModel2))
//    bh.consume(getInterpreter(multModel3))
//  }
}
