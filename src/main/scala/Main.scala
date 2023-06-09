import java.nio.file.Path

import de.szeiger.interact._

object Main extends App {
  val statements = Parser.parse(Path.of(args(0)))
  //statements.foreach(println)
  val model = new Model(statements)

  println("Constructors:")
  model.constrs.foreach(c => println(s"  ${c.show}"))
  println("Defs:")
  model.defs.foreach(d => println(s"  ${d.show}"))
  println("Rules:")
  model.rules.foreach(r => println(s"  ${r.show}"))
  //println("Data:")
  //model.data.foreach(r => println(s"  ${r.show}"))

  val inter = model.createST2Interpreter(compile = false, collectStats = true)
  model.setData(inter)
  println("Initial state:")
  inter.scope.log(System.out)
  val steps = inter.reduce()
  println(s"Irreducible after $steps reductions.")
  inter.scope.log(System.out)
}
