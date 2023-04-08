import java.nio.file.Path

import de.szeiger.interact._

object Main extends App {
  val statements = Parser.parse(Path.of(args(0)))
  //statements.foreach(println)
  val model = new Model(statements)

  println("Constructors:")
  model.constrs.values.foreach(c => println(s"  ${c.show}"))
  println("Rules:")
  model.ruleCuts.values.foreach(r => println(s"  ${r.show}"))
  println("Data:")
  model.data.foreach(r => println(s"  ${r.show}"))

  val inter = model.createMTInterpreter
  println("Initial state:")
  inter.log()
  val steps = inter.reduce()
  println(s"Irreducible after $steps reductions.")
  inter.log()
}
