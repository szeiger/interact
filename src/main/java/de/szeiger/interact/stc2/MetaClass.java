package de.szeiger.interact.stc2;

import de.szeiger.interact.ast.Symbol;

public abstract class MetaClass {
  public final Symbol cellSymbol;
  protected MetaClass(Symbol cellSymbol) {
    this.cellSymbol = cellSymbol;
  }
  public abstract void reduce(Cell thisCell, Cell otherCell, Interpreter ptw);
}
