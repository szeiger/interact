//cancelable in Global := false

scalacOptions ++= Seq("-feature")

Test / fork := true
run / fork := true
run / connectInput := true

Global / scalaVersion := "2.13.12"

lazy val main = (project in file("."))
  .settings(
    libraryDependencies += "com.github.sbt" % "junit-interface" % "0.13.2" % "test",
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "3.0.1",
    libraryDependencies ++= Seq("asm", "asm-tree", "asm-util", "asm-commons", "asm-analysis").map(a => "org.ow2.asm" % a % "9.5"),
    libraryDependencies += "com.jetbrains.intellij.java" % "java-decompiler-engine" % "233.14015.106",
    testOptions += Tests.Argument(TestFrameworks.JUnit, "-a", "-v"),
    resolvers += "IntelliJ Releases" at "https://www.jetbrains.com/intellij-repository/releases/",
    //scalacOptions ++= Seq("-feature", "-opt:l:inline", "-opt-inline-from:de.szeiger.interact.*", "-opt-inline-from:de.szeiger.interact.**"),
  )

lazy val bench = (project in file("bench"))
  .dependsOn(main)
  .enablePlugins(JmhPlugin)
  .settings(
    Jmh / javaOptions ++= Seq("-Xss32M"),
  )
