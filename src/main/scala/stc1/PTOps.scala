package de.szeiger.interact.stc1

import de.szeiger.interact.ast.PayloadType
import de.szeiger.interact.codegen.{BoxDesc, BoxOps}
import de.szeiger.interact.codegen.dsl.{Desc => tp, _}

object PTOps {
  def boxDesc(pt: PayloadType): BoxDesc = pt match {
    case PayloadType.INT => BoxDesc.intDesc
    case PayloadType.REF => BoxDesc.refDesc
    case PayloadType.LABEL => BoxDesc.refDesc
  }
  def apply(m: MethodDSL, pt: PayloadType): BoxOps = new BoxOps(m, boxDesc(pt))
}
