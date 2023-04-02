import fastparse._

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.annotation.tailrec
import scala.collection.mutable

object AST {
  sealed trait Statement
  case class Cons(name: Ident, args: Seq[Ident], ret: Option[Ident], der: Option[Deriving], rules: Seq[ConsRule]) extends Statement {
    def arity = args.length
    def show: String = {
      val a = if(args.isEmpty) "" else args.map(_.s).mkString("(", ", ", ")")
      val r = if(ret.isEmpty) "" else s" . ${ret.get.show}"
      val d = if(der.isEmpty) "" else s" deriving ${der.get.show}"
      s"${name.s}$a$r$d"
    }
  }
  sealed trait ExprOrCut {
    def show: String
  }
  sealed trait Expr extends ExprOrCut {
    def target: Ident
    def args: Seq[Expr]
  }
  case class Ident(s: String) extends Expr {
    def show = s
    def target = this
    def args = Nil
  }
  case class Ap(target: Ident, args: Seq[Expr]) extends Expr {
    def show = s"${target.show}(${args.map(_.show).mkString(", ")})"
  }
  case class Cut(left: Expr, right: Expr) extends ExprOrCut {
    def show = s"${left.show} . ${right.show}"
  }
  case class Rule(cut: Cut, reduced: Seq[Cut]) extends Statement
  case class Data(free: Seq[Ident], cuts: Seq[Cut]) extends Statement {
    def show = cuts.map(_.show).mkString(", ")
  }
  case class Deriving(constructors: Seq[Ident]) {
    def show = constructors.map(_.show).mkString(", ")
  }
  case class ConsRule(rhs: Expr, reduced: Seq[Cut])
}

object Lexical {
  import NoWhitespace._

  val keywords = Set("cons", "rule", "let", "deriving", "cut")

  def identifier[_: P]: P[String] =
     P(  (letter|"_") ~ (letter | digit | "_").rep  ).!.filter(!keywords.contains(_))
  def kw[_: P](s: String) = P(  s ~ !(letter | digit | "_")  )
  def letter[_: P] = P( CharIn("a-z") | CharIn("A-Z") )
  def digit[_: P] = P( CharIn("0-9") )
  def churchLit[_: P] = P(  digit.rep(1).! ~ "'c"  ).map(_.toInt)
}

object Parser {
  import ScriptWhitespace._
  import Lexical._

  def ident[_: P]: P[AST.Ident] = identifier.map(AST.Ident(_))

  def church[_: P]: P[AST.Expr] = churchLit.map { i =>
    (1 to i).foldLeft(AST.Ident("Z"): AST.Expr) { case (z, _) => AST.Ap(AST.Ident("S"), z :: Nil) }
  }

  def app[_: P]: P[AST.Ap] =
    P(  ident ~ "(" ~ expr.rep(sep = ",") ~ ")"  ).map(AST.Ap.tupled)

  def simpleExpr[_: P]: P[AST.Expr] =
    P(  (app | ident | church)  )

  def expr[_: P]: P[AST.Expr] =
    P(  simpleExpr.rep(1, "::")  ).map {
      case Seq(e) => e
      case es => es.foldRight(null: AST.Expr) {
        case (e, null) => e
        case (e, z) => AST.Ap(AST.Ident("Cons"), Seq(e, z))
      }
    }

  def cut[_: P]: P[AST.Cut] =
    P(expr ~ "." ~ expr).map(AST.Cut.tupled)

  def cutList[_: P]: P[Seq[AST.Cut]] =
    P(  cut.rep(min = 1, sep = ",") | P("()").map(_ => Nil)  )

  def paramsOpt[_: P]: P[Seq[AST.Ident]] =
    P(  ("(" ~ ident.rep(sep = ",") ~ ")").?  ).map(_.getOrElse(Nil))

  def deriving[_ : P]: P[AST.Deriving] =
    P(  kw("deriving") ~/ ident.rep(1, sep=",")  ).map(AST.Deriving(_))

  def consRule[_: P]: P[AST.ConsRule] =
    P(  kw("cut") ~/ expr ~ "=" ~ cutList  ).map(AST.ConsRule.tupled)

  def cons[_: P]: P[AST.Cons] =
    P(  kw("cons") ~/ ident ~ paramsOpt ~ ("." ~ ident).? ~ deriving.? ~ consRule.rep  ).map(AST.Cons.tupled)

  def rule[_: P]: P[AST.Rule] =
    P(  kw("rule") ~/ cut ~ "=" ~ cutList  ).map(AST.Rule.tupled)

  def data[_: P]: P[AST.Data] =
    P(  kw("let") ~/ ident.rep(1, sep = ",") ~ "=" ~ cutList ).map(AST.Data.tupled)

  def unit[_: P]: P[Seq[AST.Statement]] =
    P(  Start ~ (cons | rule | data).rep ~ End  )
}

object Main extends App {
  val input = new String(Files.readAllBytes(Path.of("test.in")), StandardCharsets.UTF_8)
  val statements = parse(input, Parser.unit(_), verboseFailures = true).get.value
  //statements.foreach(println)

  class RuleKey(_name1: AST.Ident, _name2: AST.Ident) {
    val (name1, name2) =
      if(_name1.s.compareTo(_name2.s) <= 0) (_name1, _name2)
      else (_name2, _name1)
    override def hashCode(): Int = name1.s.hashCode() + name2.s.hashCode()
    override def equals(obj: Any): Boolean = obj match {
      case o: RuleKey => name1.s == o.name1.s && name2.s == o.name2.s
      case _ => false
    }
  }

  class CheckedRule(val r: AST.Rule, val name1: AST.Ident, val args1: Seq[AST.Ident], val name2: AST.Ident, val args2: Seq[AST.Ident]) {
    def show: String = s"${r.cut.show} = ${r.reduced.map(_.show).mkString(", ")}"
  }

  val constrs = mutable.Map.empty[AST.Ident, AST.Cons]
  val ruleCuts = mutable.Map.empty[RuleKey, CheckedRule]
  val data = mutable.ArrayBuffer.empty[AST.Data]

  def derive(cons: AST.Cons, id: AST.Ident): AST.Rule = {
    var nextId = 0
    def genId() = {
      val s = AST.Ident(s"$$s${nextId}")
      nextId += 1
      s
    }
    val (cut, reduced) = id.s match {
      case "Erase" =>
        val Erase = AST.Ident("Erase")
        val ids = (0 until cons.arity).map(_ => genId()).toArray
        val cut = AST.Cut(Erase, AST.Ap(cons.name, ids))
        val reduced = ids.map(i => AST.Cut(Erase, i))
        (cut, reduced.toSeq)
      case "Dup" =>
        val Dup = AST.Ident("Dup")
        val ids, aIds, bIds = (0 until cons.arity).map(_ => genId()).toArray
        val a, b = genId()
        val cut = AST.Cut(AST.Ap(Dup, Seq(a, b)), AST.Ap(cons.name, ids))
        val dupPorts = ids.zip(aIds).zip(bIds).map { case ((id, aId), bId) =>
          AST.Cut(AST.Ap(Dup, Seq(aId, bId)), id)
        }
        val recombA = AST.Cut(a, AST.Ap(cons.name, aIds))
        val recombB = AST.Cut(b, AST.Ap(cons.name, bIds))
        (cut, recombA :: recombB :: dupPorts.toList)
      case s => sys.error(s"Don't know how to derive ${cons.name.s} . ${id.s}")
    }
    AST.Rule(cut, reduced)
  }

  def addRule(r: AST.Rule): Unit = {
    def checkCutCell(e: AST.Expr): (AST.Ident, Seq[AST.Ident]) = e match {
      case a: AST.Ap =>
        val args = a.args.map {
          case i: AST.Ident => i
          case _ => sys.error(s"No nested patterns allowed in rule ${r.cut.show}")
        }
        (a.target, args)
      case a: AST.Ident =>
        (a, Nil)
    }
    val (n1, a1) = checkCutCell(r.cut.left)
    val (n2, a2) = checkCutCell(r.cut.right)
    val impl = new CheckedRule(r, n1, a1, n2, a2)
    val key = new RuleKey(impl.name1, impl.name2)
    if(ruleCuts.contains(key)) sys.error(s"Rule ${r.cut.show} duplicates ${impl.name1.s} . ${impl.name2.s}")
    ruleCuts.put(key, impl)
  }

  def checkLinearity(cuts: Seq[AST.Cut], free: Set[AST.Ident], globals: Symbols)(in: => String): Unit = {
    final class Usages(var count: Int = 0)
    val usages = mutable.HashMap.from(free.iterator.map(i => (i, new Usages)))
    def scan(c: AST.Cut, e: AST.Expr): Unit = {
      globals.get(e.target) match {
        case Some(g) =>
          if(!g.isCons) sys.error(s"Unexpected global non-constructor symbol $g in $in")
          if(e.args.length != g.cons.arity) sys.error(s"Wrong arity ${e.args.length} != ${g.cons.arity} when using $g in $in")
        case None =>
          if(e.isInstanceOf[AST.Ap])
            sys.error(s"Illegal use of non-constructor symbol ${e.target.show} as constructor in $in")
          usages.getOrElseUpdate(e.target, new Usages).count += 1
      }
      e.args.foreach(a => scan(c, a))
    }
    cuts.foreach { c =>
      scan(c, c.left)
      scan(c, c.right)
    }
    val badFree = free.iterator.map(i => (i, usages(i))).filter(_._2.count != 1).toSeq
    if(badFree.nonEmpty) sys.error(s"Non-linear use of free ${badFree.map(_._1.show).mkString(", ")} in $in")
    free.foreach(usages.remove)
    val badLocal = usages.filter(_._2.count != 2).toSeq
    if(badLocal.nonEmpty) sys.error(s"Non-linear use of local ${badLocal.map(_._1.show).mkString(", ")} in $in")
  }

  statements.foreach {
    case c: AST.Cons =>
      if(constrs.contains(c.name)) sys.error(s"Duplicate cons: ${c.name.s}")
      constrs.put(c.name, c)
      c.der.foreach { der =>
        der.constructors.foreach(i => addRule(derive(c, i)))
      }
      c.rules.foreach { m =>
        addRule(AST.Rule(AST.Cut(AST.Ap(c.name, c.args), m.rhs), m.reduced))
      }
    case r: AST.Rule => addRule(r)
    case d: AST.Data => data.addOne(d)
  }

  val globals = new Symbols
  constrs.values.foreach { c =>
    globals.getOrAdd(c.name).cons = c
  }

  data.foreach { d =>
    val freeSet = d.free.toSet
    if(freeSet.size != d.free.size) sys.error(s"Duplicate free symbol in ${d.show}")
    checkLinearity(d.cuts, freeSet, globals)(d.show)
  }
  ruleCuts.foreach { case (rk, cr) =>
    val free = cr.args1 ++ cr.args2
    val freeSet = free.toSet
    if(freeSet.size != free.size) sys.error(s"Duplicate free symbol in ${cr.show}")
    checkLinearity(cr.r.reduced, freeSet, globals)(cr.show)
  }

  println("Constructors:")
  constrs.values.foreach(c => println(s"  ${c.show}"))
  println("Rules:")
  ruleCuts.values.foreach(r => println(s"  ${r.show}"))
  println("Data:")
  data.foreach(r => println(s"  ${r.show}"))

  val inter = new Interpreter(globals, ruleCuts.values)
  data.foreach(d => inter.add(d.cuts, new Symbols(Some(globals))))
  inter.log()
  inter.reduce()
}

class Symbol(val id: AST.Ident) {
  var refs = 0
  var cons: AST.Cons = null
  def isCons = cons != null
  override def toString = id.show
}

class Symbols(parent: Option[Symbols] = None) {
  private val syms = mutable.HashMap.empty[AST.Ident, Symbol]
  def getOrAdd(id: AST.Ident): Symbol = {
    val so = parent match {
      case Some(p) => p.syms.get(id)
      case None => None
    }
    so.getOrElse(syms.getOrElseUpdate(id, new Symbol(id)))
  }
  def get(id: AST.Ident): Option[Symbol] = {
    val so = parent match {
      case Some(p) => p.syms.get(id)
      case None => None
    }
    so.orElse(syms.get(id))
  }
  def apply(id: AST.Ident): Symbol =
    get(id).getOrElse(sys.error(s"No symbol found for ${id.show}"))
}

trait Target {
  var principal: (Target, Int) = _
  def connect(slot: Int, t: Target, tslot: Int): Unit = {
    assert(slot == 0)
    principal = (t, tslot)
  }
  def getPort(slot: Int): (Target, Int) = {
    assert(slot == 0)
    principal
  }
}

final class Wire(val sym: Symbol) extends Target

final class Cell(val sym: Symbol, val arity: Int) extends Target {
  var aux = new Array[(Target, Int)](arity)
  override def connect(slot: Int, t: Target, tslot: Int) = {
    if(slot != 0) aux(slot-1) = (t, tslot)
    else super.connect(slot, t, tslot)
  }
  override def getPort(slot: Int): (Target, Int) = {
    if(slot != 0) aux(slot-1)
    else super.getPort(slot)
  }
}

class Scope {
  val cells = mutable.HashSet.empty[Cell]
  val freeWires = mutable.HashSet.empty[Wire]

  private def addSymbols(cs: Iterable[AST.Cut], symbols: Symbols): Unit = {
    def f(e: AST.Expr): Unit = e match {
      case i: AST.Ident =>
        val s = symbols.getOrAdd(i)
        if(!s.isCons) s.refs += 1
      case AST.Ap(i, es) => f(i); es.foreach(f)
    }
    cs.foreach { c => f(c.left); f(c.right) }
  }

  def add(cuts: Iterable[AST.Cut], syms: Symbols): Unit = {
    addSymbols(cuts, syms)
    val bind = mutable.HashMap.empty[Symbol, Wire]
    def create(e: AST.Expr): (Target, Int) = e match {
      case i: AST.Ident =>
        val s = syms.getOrAdd(i)
        if(s.isCons) {
          val s = syms.getOrAdd(i)
          val c = new Cell(s, s.cons.arity)
          cells.addOne(c)
          (c, 0)
        } else if(s.refs == 1) {
          val w = new Wire(s)
          freeWires.addOne(w)
          (w, 0)
        } else if(s.refs == 2) {
          bind.get(s) match {
            case Some(w) =>
              w.principal
            case None =>
              val w = new Wire(s)
              bind.put(s, w)
              (w, 0)
          }
        } else sys.error(s"Non-linear use of ${i.show} in data")
      case AST.Ap(i, args) =>
        val s = syms.getOrAdd(i)
        assert(s.isCons)
        val c = new Cell(s, s.cons.arity)
        cells.addOne(c)
        args.zipWithIndex.foreach { case (a, idx) =>
          val slot = idx + 1
          val (at, as) = create(a)
          c.connect(slot, at, as)
          at.connect(as, c, slot)
        }
        (c, 0)
    }
    def createCut(e: AST.Cut): Unit = {
      val (lt, ls) = create(e.left)
      val (rt, rs) = create(e.right)
      lt.connect(ls, rt, rs)
      rt.connect(rs, lt, ls)
      null
    }
    cuts.foreach(createCut)
  }

  private def chainStart(c: Cell): Cell = {
    val visited = mutable.HashSet.empty[Cell]
    @tailrec def f(c: Cell): Cell = c.principal match {
      case null => c
      case (p: Cell, ps) if ps != 0 && !visited.contains(p) =>
        visited.addOne(c)
        f(p)
      case _ => c
    }
    f(c)
  }

  object Church {
    def unapply(c: Cell): Option[Int] = {
      if(c.sym.id.s == "Z" && c.arity == 0) Some(0)
      else if(c.sym.id.s == "S" && c.arity == 1) {
        c.getPort(1) match {
          case (c2: Cell, 0) => unapply(c2).map(_ + 1)
          case _ => None
        }
      } else None
    }
  }

  def log(): Unit = {
    println(s"Free wires: ${freeWires.map(_.sym).mkString(", ")}")
    val rem = mutable.HashSet.from(cells)
    val helpers = mutable.HashMap.empty[(Target, Int), String]
    var nextHelper = 0
    def removeChurch(c: Cell): Unit = {
      rem.remove(c)
      if(c.arity > 0) removeChurch(c.getPort(1)._1.asInstanceOf[Cell])
    }
    def targetOrReplacement(t: Target, p: Int): String = {
      if(p == 0) show(t) else {
        helpers.get((t, p)) match {
          case Some(s) => s
          case None =>
            val s = s"$$${nextHelper}"
            nextHelper += 1
            helpers.put(t.getPort(p), s)
            s
        }
      }
    }
    def show(t: Target): String = t match {
      case c @ Church(i) =>
        removeChurch(c)
        s"$i'c"
      case c: Cell =>
        if(!rem.contains(c)) "<error: duplicate>"
        else {
          rem.remove(c)
          if(c.sym.id.s == "Cons" && c.arity == 2 && c.aux(0)._2 == 0 && c.aux(1)._2 == 0) {
            val lhs = targetOrReplacement(c.aux(0)._1, c.aux(0)._2)
            val rhs = targetOrReplacement(c.aux(1)._1, c.aux(1)._2)
            s"$lhs :: $rhs"
          } else if(c.arity == 0) c.sym.toString
          else c.aux.map { case (t, p) => targetOrReplacement(t, p) }.mkString(s"${c.sym}(", ", ", ")")
        }
      case w: Wire => w.sym.toString
    }
    println("Cells:")
    while(rem.nonEmpty) {
      val c = chainStart(rem.head)
      val p = c.principal match {
        case null => ""
        case (w: Wire, _) => s"${w.sym} . "
        case (t, p) => helpers.get((t, p)) match {
          case Some(s) => s"$s . "
          case None =>
            val s = s"$$${nextHelper}"
            nextHelper += 1
            helpers.put(t.getPort(p), s)
            s"$s . "
        }
      }
      println(s"- $p${show(c)}")
    }
  }
}

class Interpreter(globals: Symbols, rules: Iterable[Main.CheckedRule]) extends Scope {

  final class CutKey(val c1: Cell, val c2: Cell) {
    override def hashCode(): Int = c1.hashCode() + c2.hashCode()
    override def equals(obj: Any): Boolean = obj match {
      case o: CutKey => (c1 == o.c1) && (c2 == o.c2) || (c1 == o.c2) && (c2 == o.c1)
      case _ => false
    }
    def ruleKey: RuleKey = new RuleKey(c1.sym, c2.sym)
  }

  final class RuleKey(val s1: Symbol, val s2: Symbol) {
    override def hashCode(): Int = s1.hashCode() + s2.hashCode()
    override def equals(obj: Any): Boolean = obj match {
      case o: RuleKey => (s1 == o.s1) && (s2 == o.s2) || (s1 == o.s2) && (s2 == o.s1)
      case _ => false
    }
    override def toString = s"$s1 . $s2"
  }

  class RuleImpl(val r: AST.Rule, val reduced: Seq[AST.Cut], val args1: Seq[AST.Ident], val args2: Seq[AST.Ident], val key: RuleKey) {
    def args1For(k: RuleKey) = if(k.s1 == key.s1) args1 else args2
    def args2For(k: RuleKey) = if(k.s1 == key.s1) args2 else args1
  }

  def reduce(): Unit = {
    val ruleImpls = new mutable.HashMap[RuleKey, RuleImpl]
    rules.foreach { cr =>
      val s1 = globals(cr.name1)
      val s2 = globals(cr.name2)
      val rk = new RuleKey(s1, s2)
      ruleImpls.put(rk, new RuleImpl(cr.r, cr.r.reduced, cr.args1, cr.args2, rk))
    }
    val cuts = mutable.HashSet.empty[CutKey]
    cells.foreach { c =>
      c.principal match {
        case (c2: Cell, 0) =>
          val rk = new RuleKey(c.sym, c2.sym)
          if(ruleImpls.contains(rk))
            cuts.addOne(new CutKey(c, c2))
        case _ =>
      }
    }
    var steps = 0
    while(!cuts.isEmpty) {
      //println(s"Remaining reducible cuts: ${cuts.size}")
      steps += 1
      val c = cuts.head
      cuts.remove(c)
      val r = ruleImpls(c.ruleKey)
      //println(s"Reducing $c with ${r.r.name.s}: ${c.ruleKey}")
      val syms = new Symbols(Some(globals))
      val sc = new Scope
      sc.add(r.reduced, syms)
      //println("***** Reduction:")
      //sc.log()
      val a1 = r.args1For(c.ruleKey).map(syms.getOrAdd)
      val a2 = r.args2For(c.ruleKey).map(syms.getOrAdd)
      val v1 = a1.zipWithIndex.map { case (s, i) => (s, c.c1.getPort(i+1)) }
      val v2 = a2.zipWithIndex.map { case (s, i) => (s, c.c2.getPort(i+1)) }
      val bind = (v1 ++ v2).toMap
      assert(bind.keys.toSet == sc.freeWires.map(_.sym))
      cells.remove(c.c1)
      cells.remove(c.c2)
      cells.addAll(sc.cells)
      sc.freeWires.foreach { w =>
        val (b, bp) = bind(w.sym)
        val (n, np) = w.principal
        b.connect(bp, n, np)
        n.connect(np, b, bp)
        if(bp == 0 && np == 0 && b.isInstanceOf[Cell] && n.isInstanceOf[Cell]) {
          val ck = new CutKey(b.asInstanceOf[Cell], n.asInstanceOf[Cell])
          if(ruleImpls.contains(ck.ruleKey))
            cuts.addOne(ck)
        }
      }
      //println("**** After reduction:")
    }
    println(s"Irreducible after $steps reductions.")
    log()
  }
}
