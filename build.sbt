ThisBuild / version := "0.1.0"

ThisBuild / scalaVersion := "2.13.8"

lazy val root = (project in file("."))
  .settings(
    name := "z3-scala"
  )

resolvers += Resolver.mavenLocal

libraryDependencies += "com.microsoft" % "z3" % "4.9.1"

scalacOptions ++= Seq(
  "-feature",
  "-language:implicitConversions"
)
