package de.szeiger.interact

abstract class Colors {
  def cNormal: String
  def cBlack: String
  def cRed: String
  def cGreen: String
  def cYellow: String
  def cBlue: String
  def cMagenta: String
  def cCyan: String
  def bRed: String
  def bGreen: String
  def bYellow: String
  def bBlue: String
  def bMagenta: String
  def bCyan: String
}

object MaybeColors extends Colors {
  val useColors: Boolean = System.getProperty("interact.colors", "true").toBoolean

  val (cNormal, cBlack, cRed, cGreen, cYellow, cBlue, cMagenta, cCyan) =
    if(useColors) ("\u001B[0m", "\u001B[30m", "\u001B[31m", "\u001B[32m", "\u001B[33m", "\u001B[34m", "\u001B[35m", "\u001B[36m")
    else ("", "", "", "", "", "", "", "")
  val (bRed, bGreen, bYellow, bBlue, bMagenta, bCyan) =
    if(useColors) ("\u001B[41m", "\u001B[42m", "\u001B[43m", "\u001B[44m", "\u001B[45m", "\u001B[46m")
    else ("", "", "", "", "", "")
}

object NoColors extends Colors {
  val cNormal, cBlack, cRed, cGreen, cYellow, cBlue, cMagenta, cCyan, bRed, bGreen, bYellow, bBlue, bMagenta, bCyan = ""
}
