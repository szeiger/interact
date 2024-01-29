package de.szeiger.interact

import de.szeiger.interact.ast._

import java.io.{PrintWriter, StringWriter}
import scala.collection.mutable.ArrayBuffer
import scala.util.control.NonFatal

final class Global(val config: Config) {
  final val globalSymbols = new Symbols

  private[this] var hasErrors: Boolean = false
  private[this] val accumulated = ArrayBuffer.empty[Notice]

  def dependencyLoader: ClassLoader = getClass.getClassLoader

  def warning(msg: String, at: Node): Unit = error(msg, at.pos)
  def warning(msg: String, at: Position): Unit =
    accumulated += new Notice(msg, at, Severity.Warning)

  def error(msg: String, at: Node): Unit = error(msg, at.pos)
  def error(msg: String, at: Position): Unit = {
    accumulated += new Notice(msg, at, Severity.Error)
    hasErrors = true
  }

  def throwError(msg: String, at: Node): Nothing = throwError(msg, at.pos)
  def throwError(msg: String, at: Position): Nothing = {
    error(msg, at)
    throw new ReportedError
  }
  def tryError[T](f: => T): Option[T] = try Some(f) catch { case _: ReportedError => None }

  def fatal(msg: String, at: Node): Nothing = fatal(msg, at.pos)
  def fatal(msg: String, at: Position): Nothing = {
    accumulated += new Notice(msg, at, Severity.Fatal)
    throw getCompilerResult()
  }

  def internalError(msg: String, at: Position, parent: Throwable = null, atNode: Node = null): Unit = {
    accumulated += new Notice(msg, if(at == null && atNode != null) atNode.pos else at, Severity.Fatal, atNode, internal = true)
    throw getCompilerResult(parent)
  }

  def mkLocalId(name: String, isEmbedded: Boolean = false, payloadType: PayloadType = PayloadType.VOID): Ident = {
    val i = Ident(name)
    i.sym = new Symbol(name, isEmbedded = isEmbedded, payloadType = payloadType)
    i
  }

  def getCompilerResult(parent: Throwable = null): CompilerResult = new CompilerResult(accumulated.toIndexedSeq, parent)

  def checkThrow(): Unit =
    if(hasErrors) throw getCompilerResult()
}

class Notice(msg: String, at: Position, severity: Severity, atNode: ShowableNode = null, internal: Boolean = false) {
  def formatted: String = {
    import MaybeColors._
    import Notice._
    val b = new StringBuilder
    val sev = if(internal) s"${cRed}Internal Error" else if(isError) s"${cRed}Error" else s"${cYellow}Warning"
    val msgLines = msg.split('\n')
    if(at.isDefined) {
      val (line, col) = at.input.find(at.offset)
      b.append(s"$sev: $cNormal${at.file}$cCyan:${line+1}:${col+1}$cNormal: ${msgLines.head}$eol")
      msgLines.tail.foreach { m => b.append(s"$cBlue| $cNormal$m$eol") }
      b.append(s"$cBlue| $cNormal${at.input.getLine(line).stripTrailing()}$eol")
      b.append(s"$cBlue| $cGreen${at.input.getCaret(col)}$cNormal")
    } else {
      b.append(s"$sev: $cNormal ${msgLines.head}$eol")
      msgLines.tail.foreach { m => b.append(s"$cBlue| $cNormal$m$eol") }
    }
    if(internal && atNode != null) {
      val out = new StringWriter()
      val outw = new PrintWriter(out)
      outw.print(s"\n$cBlue| ${cRed}AST Context:$cNormal\n")
      ShowableNode.print(atNode, outw, prefix = s"$cBlue|   ")
      b.append(out.toString)
    }
    b.result()
  }
  override def toString: String = formatted
  def isError: Boolean = severity != Severity.Warning
}

object Notice {
  val eol: String = sys.props("line.separator")
}

sealed abstract class Severity
object Severity {
  case object Warning extends Severity
  case object Error extends Severity
  case object Fatal extends Severity
}

class CompilerResult(val notices: IndexedSeq[Notice], parent: Throwable = null) extends Exception(parent) {
  lazy val hasErrors = notices.exists(_.isError)
  lazy val summary: String = {
    val errs = notices.count(_.isError)
    val warns = notices.length - errs
    def fmt(i: Int, s: String) = if(i == 1) s"1 $s" else s"$i ${s}s"
    if(warns > 0) s"${fmt(errs, "error")}, ${fmt(warns, "warnings")} found."
    else s"${fmt(errs, "error")} found."
  }
  override def getMessage: String = {
    import Notice._
    val b = (new StringBuilder).append(eol)
    notices.foreach(n => b.append(n.formatted).append(eol).append(eol))
    b.append(summary).result()
  }
}
object CompilerResult {
  def tryInternal[T](at: Position)(f: => T): T = try f catch {
    case e: CompilerResult => throw e
    case e: AssertionError => throw new CompilerResult(Vector(new Notice(e.toString, at, Severity.Fatal, internal = true)), e)
    case NonFatal(e) => throw new CompilerResult(Vector(new Notice(e.toString, at, Severity.Fatal, internal = true)), e)
  }
  def tryInternal[T](atNode: Node)(f: => T): T = try f catch {
    case e: CompilerResult => throw e
    case e: AssertionError => throw new CompilerResult(Vector(new Notice(e.toString, atNode.pos, Severity.Fatal, internal = true, atNode = atNode)), e)
    case NonFatal(e) => throw new CompilerResult(Vector(new Notice(e.toString, atNode.pos, Severity.Fatal, internal = true, atNode = atNode)), e)
  }

  def fail(msg: String, at: Position = null, parent: Throwable = null, atNode: Node = null, internal: Boolean = true): Nothing =
    throw new CompilerResult(Vector(new Notice(msg, if(at == null && atNode != null) atNode.pos else at, Severity.Fatal, atNode, internal)))
}

class ReportedError extends Exception("Internal error: ReportedError thrown by throwError must be caught by a surrounding tryError")

trait BaseInterpreter {
  def getAnalyzer: Analyzer[_]
  def initData(): Unit
  def reduce(): Unit
  def getMetrics: ExecutionMetrics
}
