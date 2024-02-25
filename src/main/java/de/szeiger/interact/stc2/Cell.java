package de.szeiger.interact.stc2;

public abstract class Cell {
  public Cell() {}
  public abstract Cell auxCell(int p);
  public abstract int auxPort(int p);
  public abstract void setAux(int p, Cell c2, int p2);
  public MetaClass metaClass;
}
