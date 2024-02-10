package de.szeiger.interact.codegen

import de.szeiger.interact.Config
import org.jetbrains.java.decompiler.main.decompiler.ConsoleDecompiler

import java.io.{File, FileOutputStream}
import java.nio.file.{Files, Path}
import java.util.jar.{JarEntry, JarOutputStream}

trait ClassWriter { self =>
  def writeClass(javaName: String, classFile: Array[Byte]): Unit
  def close(): Unit = ()

  def and(w: ClassWriter): ClassWriter = new ClassWriter {
    def writeClass(javaName: String, classFile: Array[Byte]): Unit = {
      self.writeClass(javaName, classFile)
      w.writeClass(javaName, classFile)
    }
    override def close(): Unit = {
      self.close()
      w.close()
    }
  }
}

final class NullClassWriter extends ClassWriter {
  def writeClass(javaName: String, classFile: Array[Byte]): Unit = ()
}

final class JarClassWriter(file: Path) extends ClassWriter {
  if(Files.exists(file)) Files.delete(file)
  private[this] val out = new JarOutputStream(new FileOutputStream(file.toFile))
  private[this] var closed = false

  def writeClass(javaName: String, classFile: Array[Byte]): Unit = {
    assert(!closed)
    out.putNextEntry(new JarEntry(javaName.replace('.', '/')+".class"))
    out.write(classFile)
    out.closeEntry()
  }

  override def close(): Unit = {
    out.close()
    closed = true
  }
}

final class ClassDirWriter(dir: Path) extends ClassWriter {
  ClassWriter.delete(dir)

  def writeClass(javaName: String, classFile: Array[Byte]): Unit = {
    val p = javaName.split('.').foldLeft(dir) { case (p, s) => p.resolve(s) }
    Files.createDirectories(p.getParent)
    val f = p.resolveSibling(p.getFileName + ".class")
    Files.write(f, classFile)
  }
}

private final class DecompileAdapter(parent: ClassWriter, classes: Path, out: Path) extends ClassWriter {
  def writeClass(javaName: String, classFile: Array[Byte]): Unit = parent.writeClass(javaName, classFile)

  override def close(): Unit = {
    parent.close()
    ClassWriter.delete(out)
    Files.createDirectories(out)
    val args = Array(classes.toAbsolutePath.toFile.getPath, out.toAbsolutePath.toFile.getPath)
    ConsoleDecompiler.main(args)
  }
}

object ClassWriter {
  private[codegen] def delete(p: Path): Unit = if(Files.exists(p)) {
    if(Files.isDirectory(p)) Files.list(p).forEach(delete)
    Files.delete(p)
  }

  def apply(config: Config, parent: ClassWriter): ClassWriter = {
    val p = if(config.skipCodeGen) new NullClassWriter else parent
    val cw: ClassWriter = config.writeOutput match {
      case Some(f) if f.getFileName.toString.endsWith(".jar") => p.and(new JarClassWriter(f))
      case Some(f) => p.and(new ClassDirWriter(f))
      case None => p
    }
    (config.writeJava, config.writeOutput) match {
      case (Some(classes), None) => ???
      case (Some(sources), Some(classes)) => new DecompileAdapter(cw, classes, sources)
      case _ => cw
    }
  }
}
