ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.3.3"
ThisBuild / scalacOptions ++= Seq(
  "-encoding",
  "UTF-8",
  "-deprecation",
  "-feature",
  // "-Xprint:typer",
  // "-explain",
  "-Xcheck-macros",
  "-Ycheck:all", // also for checking macros
  "-Ycheck-mods",
  "-Ydebug-type-error",
  "-Xprint-types", // Without this flag, we will not see error messages for exceptions during given-macro expansion!
  "-Yshow-print-errors",
  "-language:experimental.macros",
  "-language:implicitConversions",
  "-language:higherKinds",
  "-language:namedTypeArguments",
  "-language:saferExceptions",
  "-language:dynamics",
  "-language:numericLiterals",
  // "-Ykind-projector:underscores",
  "-unchecked",
  // "-Ysafe-init", // Note: causes warnings when used with Shapeless 3 recursive derivation
  // "-Yexplicit-nulls", // Make reference types non-nullable: String != String|Null
  "-Wnonunit-statement",
  "-Wvalue-discard"
  /*
  NOT YET IMPLEMENTED IN SCALA 3.3.1
  "-Wself-implicit", // Warn when an implicit resolves to an enclosing self-definition
   */
  // "-source",
  // "future-migration" // needed for warnings about matching types that are not `Matchable`
)

lazy val root = (project in file("."))
  .settings(
    name := "hkd4s",
    idePackagePrefix := Some("com.tschuchort.hkd"),
    resolvers ++= Seq(
      Resolver.sonatypeOssRepos("releases"),
      Resolver.sonatypeOssRepos("snapshots")
    ).flatten,
    libraryDependencies ++= Seq(
      "org.typelevel" %% "cats-core" % "2.12.0",
      "org.typelevel" %% "alleycats-core" % "2.12.0",
      "org.typelevel" %% "mouse" % "1.2.3", // helper functions
      "org.typelevel" %% "kittens" % "3.3.0", // type class derivation
      "org.typelevel" %% "cats-collections-core" % "0.9.8",
      "org.typelevel" %% "shapeless3-deriving" % "3.4.1",
      "org.typelevel" %% "shapeless3-typeable" % "3.4.1",
      "dev.zio" %% "izumi-reflect" % "2.3.9"
    ),
    // Test dependencies
    libraryDependencies ++= Seq(
      "org.scalameta" %% "munit" % "1.0.0"
    ).map(_ % Test),
    Test / parallelExecution := true
  )
