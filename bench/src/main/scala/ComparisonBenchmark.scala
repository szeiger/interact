package de.szeiger.interact

import org.openjdk.jmh.annotations._
import org.openjdk.jmh.infra._

import java.util.concurrent.TimeUnit

@BenchmarkMode(Array(Mode.Throughput))
@Fork(value = 1, jvmArgsAppend = Array("-Xmx12g", "-Xss32M", "-XX:+UnlockExperimentalVMOptions", "-XX:+UseZGC"))
@Threads(1)
@Warmup(iterations = 15, time = 1)
@Measurement(iterations = 15, time = 1)
@OutputTimeUnit(TimeUnit.SECONDS)
@State(Scope.Benchmark)
class ComparisonBenchmark {

  @Param(Array("stc2"))
  var spec: String = _

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

  private val intAck38Src =
    """cons Int[int]
      |
      |def ackU(a, b) = r
      |  | Int[x], Int[y]
      |      if [x == 0] => Int[y + 1]
      |      if [y == 0] => ackU(Int[x - 1], Int[1])
      |      else        => ackU(Int[x - 1], ackU(Int[x], Int[y - 1]))
      |
      |let resU = ackU(Int[3], Int[9])
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

  class PreparedInterpreter(source: String) {
    val model: Compiler = new Compiler(Parser.parse(source), Config(spec))
    val inter = model.createInterpreter()
    def setup(): BaseInterpreter = {
      inter.initData()
      inter
    }
  }

  private lazy val mult1Inter: PreparedInterpreter = new PreparedInterpreter(mult1Src)
  private lazy val fib22Inter: PreparedInterpreter = new PreparedInterpreter(fib22Src)
  private lazy val intAck38Inter: PreparedInterpreter = new PreparedInterpreter(intAck38Src)
  private lazy val intMult3Inter: PreparedInterpreter = new PreparedInterpreter(intMult3Src)

  @Benchmark
  def mult1(bh: Blackhole): Unit =
    bh.consume(mult1Inter.setup().reduce())

  @Benchmark
  def fib22(bh: Blackhole): Unit =
    bh.consume(fib22Inter.setup().reduce())

  @Benchmark
  def intAck39(bh: Blackhole): Unit =
    bh.consume(intAck38Inter.setup().reduce())

  @Benchmark
  def intMult3(bh: Blackhole): Unit =
    bh.consume(intAck38Inter.setup().reduce())

  @Benchmark
  def mult1Scala(bh: Blackhole): Unit = {
    sealed abstract class Nat
    case object Z extends Nat
    case class S(pred: Nat) extends Nat
    def nat(i: Int): Nat = i match {
      case 0 => Z
      case n => S(nat(n-1))
    }
    def add(x: Nat, y: Nat): Nat = x match {
      case Z => y
      case S(x) => add(x, S(y))
    }
    def mult(x: Nat, y: Nat): Nat = x match {
      case Z => Z
      case S(x) => add(mult(x, y), y)
    }
    bh.consume(mult(nat(100), nat(100)))
  }

  @Benchmark
  def fib22Scala(bh: Blackhole): Unit = {
    sealed abstract class Nat
    case object Z extends Nat
    case class S(pred: Nat) extends Nat
    def nat(i: Int): Nat = i match {
      case 0 => Z
      case n => S(nat(n-1))
    }
    def add2(x: Nat, y: Nat): Nat = x match {
      case Z => y
      case S(x) => S(add2(x, y))
    }
    def fib(x: Nat): Nat = x match {
      case Z => nat(1)
      case S(n) => fib2(n)
    }
    def fib2(x: Nat): Nat = x match {
      case Z => nat(1)
      case S(n) => add2(fib(S(n)), fib(n))
    }
    bh.consume(fib(nat(22)))
  }

  @Benchmark
  def intAck39Scala(bh: Blackhole): Unit = {
    def ack(x: Int, y: Int): Int =
      if(x == 0) y + 1
      else if(y == 0) ack(x-1, 1)
      else ack(x-1, ack(x, y-1))
    bh.consume(ack(3, 9))
  }

  @Benchmark
  def intMult3Scala(bh: Blackhole): Unit = {
    def add(x: Int, y: Int): Int =
      if(x == 0) y
      else add(x-1, y+1)
    def mult(x: Int, y: Int): Int =
      if(x == 0) 0
      else add(y, mult(x-1, y))
    bh.consume(mult(1000, 1000))
  }
}
