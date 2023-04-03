scalaVersion in Global := "2.13.10"

cancelable in Global := false

scalacOptions ++= Seq("-feature")

fork in Test := true

lazy val main = (project in file("."))
  .settings(
    libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % "test",
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "3.0.1",
    testOptions += Tests.Argument(TestFrameworks.JUnit, "-a", "-v"),
  )

lazy val bench = (project in file("bench"))
  .dependsOn(main)
  .enablePlugins(JmhPlugin)
