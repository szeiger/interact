import java.nio.file.Path
import de.szeiger.interact._
import de.szeiger.interact.ast.ShowableNode

object Main extends App {
  def handleRes(res: CompilerResult, full: Boolean): Unit = {
    if(full) res.printStackTrace(System.out)
    else {
      res.notices.foreach(println)
      println(res.summary)
    }
    if(res.hasErrors) sys.exit(1)
  }
  try {
    val unit = Parser.parse(Path.of(args(0)))
    ShowableNode.print(unit)
    //statements.foreach(println)
    val model = new Compiler(unit)

    //println("Constructors:")
    //model.constrs.foreach(c => println(s"  ${c.show}"))
    //println("Defs:")
    //model.defs.foreach(d => println(s"  ${d.show}"))
    //println("Rules:")
    //model.rules.foreach(r => if(!r.isInstanceOf[DerivedRule]) println(s"  ${r.show}"))
    //println("Data:")
    //model.data.foreach(r => println(s"  ${r.show}"))
    //ShowableNode.print(model.unit)

    ShowableNode.print(model.unit2)
    val inter = model.createSTInterpreter(compile = false, collectStats = true)
    model.setDataIn(inter.scope)
    println("Initial state:")
    inter.scope.log(System.out)
    val steps = inter.reduce()
    println(s"Irreducible after $steps reductions.")
    inter.scope.log(System.out)
    handleRes(model.global.getCompilerResult(), false)
  } catch { case ex: CompilerResult => handleRes(ex, true) }
}
