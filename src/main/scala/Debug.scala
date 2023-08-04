import de.szeiger.interact._
import de.szeiger.interact.st2.Cell

import java.nio.file.Path
import scala.annotation.tailrec
import scala.collection.mutable

object Debug extends App {
  val statements = Parser.parse(Path.of(args(0)))
  val model = new Compiler(statements)
  val inter = model.createST2Interpreter(compile = false)
  model.setDataIn(inter.scope)

  var steps = 0
  var cuts: mutable.ArrayBuffer[Cell] = _

  @tailrec
  def readLine(): Option[Int] = {
    print("> ")
    val in = Console.in.readLine()
    if(in == "q") None
    else in.toIntOption.filter(i => i >= 0 && i < cuts.length) match {
      case None => readLine()
      case o => o
    }
  }

  @tailrec def step(): Unit = {
    println(s"${MaybeColors.cGreen}At step $steps:${MaybeColors.cNormal}")
    cuts = inter.scope.log(System.out, markCut = (c1, _) => inter.getRuleImpl(c1.pref) != null)
    if(cuts.isEmpty)
      println(s"${MaybeColors.cGreen}Irreducible after $steps reductions.${MaybeColors.cNormal}")
    steps += 1
    readLine() match {
      case None => ()
      case Some(idx) =>
        inter.reduce1(cuts(idx).pref)
        step()
    }
  }

  step()
}
