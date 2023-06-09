//scalaVersion in Global := "2.13.10"

//cancelable in Global := false

scalacOptions ++= Seq("-feature")

fork in Test := true

Global / resolvers += "scala-integration" at
  "https://scala-ci.typesafe.com/artifactory/scala-integration/"

Global / scalaVersion := "2.13.11-bin-28eef15"

lazy val main = (project in file("."))
  .settings(
    libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % "test",
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "3.0.1",
    libraryDependencies ++= Seq("asm", "asm-tree", "asm-util", "asm-commons", "asm-analysis").map(a => "org.ow2.asm" % a % "9.5"),
    testOptions += Tests.Argument(TestFrameworks.JUnit, "-a", "-v"),
    scalacOptions ++= Seq("-feature", "-opt:l:inline", "-opt-inline-from:de.szeiger.interact.*", "-opt-inline-from:de.szeiger.interact.**"),
  )

lazy val bench = (project in file("bench"))
  .dependsOn(main)
  .enablePlugins(JmhPlugin)
