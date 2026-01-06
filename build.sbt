name := "trepplein"
description := "Independent type-checker for the dependently typed theorem prover Lean 4"
homepage := Some(url("https://github.com/gebner/trepplein"))
startYear := Some(2017)
licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html"))
maintainer := "gebner@gebner.org"

version := "2.0-SNAPSHOT"

scalaVersion := "3.3.7"

libraryDependencies ++= Seq(
  "com.github.scopt" %% "scopt" % "4.1.0",
  "org.specs2" %% "specs2-core" % "5.5.8" % Test,
  "io.spray" %% "spray-json" % "1.3.6"  // For NDJSON support
)

scalacOptions ++= Seq(
  "-deprecation",
  "-feature",
  "-unchecked"
)

enablePlugins(JavaAppPackaging)
Universal / javaOptions ++= Seq("-J-Xss30m", "-J-Xmx16g")

// Fork to enable larger stack size for deeply nested expressions
run / fork := true
run / javaOptions ++= Seq("-Xss30m", "-Xmx16g")
