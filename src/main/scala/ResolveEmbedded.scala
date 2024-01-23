package de.szeiger.interact

import de.szeiger.interact.ast._

import java.lang.reflect.Method

/** Resolve embedded methods and assign embedded types. */
class ResolveEmbedded(global: Global) extends Transform with Phase {
  import global._

  override def apply(_n: Branch): Branch = {
    val n2 = super.apply(_n)
    n2.cond.foreach { ee =>
      val (tp, _) = getReturnType(ee)
      if(tp != EmbeddedType.Bool)
        error(s"Expected boolean type for condition expression, got $tp", ee)
    }
    n2
  }

  override def apply(_n: EmbeddedApply): EmbeddedApply = {
    val n2 = super.apply(_n)
    val args = n2.args.map(getReturnType)
    val (clsName, mName, qn) = {
      if(n2.op && args.length == 2 && args(0)._1 == EmbeddedType.PayloadLabel && args(1)._1 == EmbeddedType.PayloadLabel) ResolveEmbedded.eqLabel
      else if(n2.op) ResolveEmbedded.operators(n2.methodQN.head)
      else (n2.className, n2.methodName, n2.methodQNIds)
    }
    val methTp = resolveMethod(n2, clsName, mName, args)
    val n3 = n2.copy(methodQNIds = qn, embTp = methTp, op = false)
    //ShowableNode.print(n3, name = "Resolved")
    n3
  }

  private[this] def getReturnType(ee: EmbeddedExpr): (EmbeddedType, Boolean /* out */) = ee match {
    case _: StringLit => (EmbeddedType.PayloadRef, false)
    case _: IntLit => (EmbeddedType.PayloadInt, false)
    case ee: Ident => (EmbeddedType.Payload(ee.sym.payloadType), !ee.sym.isPattern)
    case ee: EmbeddedApply => (ee.embTp match {
      case t: EmbeddedType.Method => t.ret
      case t @ EmbeddedType.Unknown => t
    }, false)
    case _ => (EmbeddedType.PayloadVoid, false)
  }

  private[this] def resolveMethod(e: EmbeddedApply, cln: String, mn: String, args: Vector[(EmbeddedType, Boolean)]): EmbeddedType = {
    val c = dependencyLoader.loadClass(cln)
    def toPT(cl: Class[_]): (EmbeddedType, Boolean) = cl.getName match {
      case "void" => (EmbeddedType.PayloadVoid, false)
      case "int" => (EmbeddedType.PayloadInt, false)
      case "boolean" => (EmbeddedType.Bool, false)
      case s if s == classOf[IntOutput].getName => (EmbeddedType.PayloadInt, true)
      case s if s == classOf[RefOutput].getName => (EmbeddedType.PayloadRef, true)
      case _ if !cl.isPrimitive => (EmbeddedType.PayloadRef, false)
      case s => (EmbeddedType.Unknown, false)
    }
    tryError {
      val nameCandidates = c.getDeclaredMethods.filter(_.getName == mn).map { m =>
        EmbeddedType.Method(m, toPT(m.getReturnType)._1, m.getParameterTypes.iterator.map(toPT).toVector)
      }
      val typeCandidates = nameCandidates.filter { m =>
        m.args == args.map {
          case (EmbeddedType.Payload(PayloadType.LABEL), o) => (EmbeddedType.PayloadRef, o)
          case (t, o) => (t, o)
        }
      }
      if(nameCandidates.isEmpty) throwError(s"Method $cln.$mn not found.", e)
      else if(typeCandidates.isEmpty) {
        val exp = showEmbeddedSignature(args, EmbeddedType.Unknown, mn)
        val found = nameCandidates.map(m => showJavaSignature(m.method)).mkString("  ", "\n  ", "")
        throwError(s"No applicable overload of method $cln.$mn.\nExpected:\n  $exp\nFound:\n$found", e)
      }
      else if(typeCandidates.length > 1) {
        val exp = showEmbeddedSignature(args, EmbeddedType.Unknown, mn)
        val found = nameCandidates.map(m => showJavaSignature(m.method)).mkString("  ", "\n  ", "")
        throwError(s"${typeCandidates.length} ambiguous overloads of method $cln.$mn.\nExpected:\n  $exp\nAmbiguous:\n$found", e)
      }
      else typeCandidates.head
    }.getOrElse(EmbeddedType.Unknown)
  }

  private[this] def showJavaSignature(m: Method): String = {
    s"${m.getReturnType.getName} ${m.getName}(${m.getParameterTypes.map(_.getName).mkString(", ")})"
  }

  private[this] def showEmbeddedSignature(args: Vector[(EmbeddedType, Boolean)], ret: EmbeddedType, name: String): String = {
    def f(t: EmbeddedType, out: Boolean): String = (if (out) "out " else "") + (t match {
      case EmbeddedType.Payload(pt) => pt.toString
      case EmbeddedType.Bool => "boolean"
      case EmbeddedType.Unknown => "?"
      case t => t.toString
    })
    s"${f(ret, false)} ${name}(${args.map{ case (t, o) => f(t, o) }.mkString(", ")})"
  }
}

object ResolveEmbedded {
  private[this] val runtimeName = Runtime.getClass.getName
  private[this] val intrinsicsQN = runtimeName.split('.').toVector
  private[this] def mkOp(m: String) = (runtimeName, m, (intrinsicsQN :+ m).map(Ident(_)))
  private val eqLabel = mkOp("eqLabel")
  private val operators = Map(
    "==" -> mkOp("eq"),
    "+" -> mkOp("intAdd"),
    "-" -> mkOp("intSub"),
    "*" -> mkOp("intMult"),
  )
}
