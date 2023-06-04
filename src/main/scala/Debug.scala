import de.szeiger.interact._
import de.szeiger.interact.st2.Cell

import java.nio.file.Path
import scala.annotation.tailrec
import scala.collection.mutable

object Debug extends App {
  val statements = Parser.parse(Path.of(args(0)))
  val model = new Model(statements)
  val inter = model.createST2Interpreter(compile = false)
  model.setData(inter)

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
    println(s"At step $steps:")
    cuts = inter.scope.log(System.out, markCut = (c1, _) => inter.getRuleImpl(c1.pref) != null)
    if(cuts.isEmpty)
      println(s"Irreducible after $steps reductions.")
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
