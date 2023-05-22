import de.szeiger.interact._

import java.nio.file.Path
import scala.annotation.tailrec

object Debug extends App {
  val statements = Parser.parse(Path.of(args(0)))
  val model = new Model(statements)
  val inter = model.createST2Interpreter()

  var step = 0
  var cuts = inter.scope.getCutLogs.toIndexedSeq

  @tailrec
  def readLine(): Option[Int] = {
    print("> ")
    val in = Console.in.readLine()
    if(in == "q") None
    else in.toIntOption.filter(i => i >= 0 && i < cuts.length && inter.getRuleImpl(cuts(i)._1.pref) != null) match {
      case None => readLine()
      case o => o
    }
  }

  while(cuts.nonEmpty) {
    println(s"At step $step:")
    cuts.zipWithIndex.foreach { case ((w, l, r, o), idx) =>
      val (i1, i2) = if(inter.getRuleImpl(w.pref) != null) (s"[$idx]", "   ") else ("   ", "   ")
      o match {
        case Some(r2) =>
          val (s1, s2) = if(r.length < r2.length) (r, r2) else (r2, r)
          println(s"  $i1  $s1")
          println(s"  $i2  $s2")
        case None =>
          println(s"  $i1  $l . $r")
      }
    }
    readLine() match {
      case None => cuts = IndexedSeq.empty
      case Some(idx) =>
        inter.reduce1(cuts(idx)._1.pref)
        step += 1
        cuts = inter.scope.getCutLogs.toIndexedSeq
        if(cuts.isEmpty)
          println(s"Irreducible after $step reductions.")
    }
  }
}
