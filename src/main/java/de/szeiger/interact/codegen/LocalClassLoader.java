package de.szeiger.interact.codegen;

public class LocalClassLoader extends ClassLoader {
  static { registerAsParallelCapable(); }

  public final Class<?> defineClass(String name, byte[] b) throws ClassFormatError {
    return defineClass(name, b, 0, b.length);
  }
}
