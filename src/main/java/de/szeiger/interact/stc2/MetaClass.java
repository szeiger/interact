package de.szeiger.interact.stc2;

import de.szeiger.interact.ast.Symbol;

public abstract class MetaClass {
  public final Symbol cellSymbol;
  public final int symId;
  protected MetaClass(Symbol cellSymbol, int symId) {
    this.cellSymbol = cellSymbol;
    this.symId = symId;
  }
}
