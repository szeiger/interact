package de.szeiger.interact

import de.szeiger.interact.ast._

import scala.collection.mutable.ArrayBuffer

final class Global(
  val defaultDerive: Seq[String] = Seq("erase", "dup"),
  val addEraseDup: Boolean = true
) {
  final val globalSymbols = new Symbols

  private[this] var hasErrors: Boolean = false
  private[this] val accumulated = ArrayBuffer.empty[Notice]

  def warning(msg: String, at: Node): Unit = error(msg, at.pos)
  def warning(msg: String, at: Position): Unit =
    accumulated += new Notice(msg, at, Severity.Warning)

  def error(msg: String, at: Node): Unit = error(msg, at.pos)
  def error(msg: String, at: Position): Unit = {
    accumulated += new Notice(msg, at, Severity.Error)
    hasErrors = true
  }

  def fatal(msg: String, at: Node): Unit = error(msg, at.pos)
  def fatal(msg: String, at: Position): Unit = {
    accumulated += new Notice(msg, at, Severity.Fatal)
    throw getCompilerResult()
  }

  def mkLocalId(name: String): Ident = {
    val i = Ident(name)
    i.sym = new Symbol(name)
    i
  }

  def getCompilerResult(): CompilerResult = new CompilerResult(accumulated.toIndexedSeq)

  def checkThrow(): Unit =
    if(hasErrors) throw getCompilerResult()
}

class Notice(msg: String, at: Position, severity: Severity) {
  def formatted: String = {
    import MaybeColors._
    import Notice._
    val b = new StringBuilder
    val sev = if(isError) s"${cRed}Error" else s"${cYellow}Warning"
    if(at.isDefined) {
      val (line, col) = at.input.find(at.offset)
      b.append(s"$sev: $cNormal${at.file}$cCyan:${line+1}:${col+1}$cNormal: $msg$eol")
      b.append(s"$cBlue| $cNormal${at.input.getLine(line)}$eol")
      b.append(s"$cBlue| $cGreen${at.input.getCaret(col)}$cNormal")
    } else {
      b.append(s"$sev: $cNormal $msg$eol")
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

class CompilerResult(val notices: IndexedSeq[Notice]) extends Exception {
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
    val b = new StringBuilder
    notices.foreach(n => b.append(n.formatted).append(eol))
    b.append(summary).result()
  }
}
