import com.jsuereth.sbtpgp.PgpKeys.signedArtifacts

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
  //"-language:namedTypeArguments",
  //"-language:saferExceptions",
  "-language:dynamics",
  //"-language:numericLiterals",
  "-Xkind-projector:underscores",
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
    description := "Higher Kinded Data for Scala 3",

    // Organization and developer info is mandatory in POM for Maven Central!
    organization := "com.github.tschuchortdev" ,
    organizationName := "tschuchortdev",
    organizationHomepage := Some(url("https://github.com/tschuchortdev")),
    homepage := scmInfo.value.map(_.browseUrl),
    developers := List(Developer(
        id    = "tschuchortdev",
        name  = "Thilo Schuchort",
        email = "t.schuchort@googlemail.com",
        url   = url("https://github.com/tschuchortdev")
    )),

    scmInfo := Some(ScmInfo(
        url("https://github.com/tschuchortdev/hkd4s"),
        "scm:git@github.com:tschuchortdev/hkd4s.git"
    )),

    pgpSigningKey := Some("98C8EE4707346CDA0EEDDD624ACC18C2ABB7F7CC"),
    // PGP signing key password given either through env var PGP_PASSPHRASE or through input dialog
    // The secret key must be present in the GPG keyring.

    licenses := List("MIT" -> new URL("https://opensource.org/license/mit")),

    pomIncludeRepository := { _ => false },

    resolvers ++= Seq(
      Resolver.sonatypeOssRepos("releases"),
      Resolver.sonatypeOssRepos("snapshots")
    ).flatten,

    publishMavenStyle := true,
    versionScheme := Some("early-semver"),

    // This will make it so that non-SNAPSHOT releases are published to a local folder, so that they can then
    // be bulk-uploaded by sonatypeBundleRelease command, which is much faster than uploading every file separately
    publishTo := sonatypePublishToBundle.value,

    sonatypeProfileName := "com.github.tschuchortdev",

    credentials +=
      Credentials("Sonatype Nexus Repository Manager",
        "oss.sonatype.org",
        sys.env.getOrElse("SONATYPE_NEXUS_USERNAME", ""),
        sys.env.getOrElse("SONATYPE_NEXUS_PASSWORD", "")
      ),

    libraryDependencies ++= Seq(
      "org.typelevel" %% "cats-core" % "2.12.0",
      "org.typelevel" %% "alleycats-core" % "2.12.0", // Needed for Pure type class
      "org.typelevel" %% "shapeless3-deriving" % "3.4.1",
      "dev.zio" %% "izumi-reflect" % "2.3.10"
    ),
    // Test dependencies
    libraryDependencies ++= Seq(
      "org.scalameta" %% "munit" % "1.0.0",
      "org.typelevel" %% "mouse" % "1.3.1", // helper functions
      "org.typelevel" %% "kittens" % "3.3.0", // type class derivation
      "org.typelevel" %% "cats-collections-core" % "0.9.8",
      "org.typelevel" %% "cats-effect" % "3.5.7"
    ).map(_ % Test),

    Test / parallelExecution := true
  )

Global / onChangedBuildSource := ReloadOnSourceChanges
Global / excludeLintKeys  += idePackagePrefix

// Safety check that the version string is computed from git tags
// Will fail build import if there is no initial tag!
Global / onLoad := (Global / onLoad).value.andThen { s =>
  dynverAssertTagVersion.value
  s
}

inThisBuild(List(
  version := makeVersionString(dynverGitDescribeOutput.value, dynverCurrentDate.value),
  dynver := {
    val date = new java.util.Date
    makeVersionString(sbtdynver.DynVer.getGitDescribeOutput(date), date)
  }
))

def makeVersionString(gitOutput: Option[sbtdynver.GitDescribeOutput], date: java.util.Date): String = {
  gitOutput match {
    // isTag == previous git tag was found, must not be exactly at this commit
    case Some(gitOutput) if gitOutput.ref.isTag =>
      if (gitOutput.isCleanAfterTag) // cleanAfterTag == no committed or uncommitted changes since last tag
        gitOutput.ref.dropPrefix // ref is actually the tag that was found
      else {
        val semverPattern = "^(\\d+)\\.(\\d+)\\.(\\d+)$".r
        gitOutput.ref.dropPrefix match {
          case semverPattern (major, minor, patch) =>
            val incPatch = patch.toInt + 1
            s"$major.$minor.$incPatch-SNAPSHOT"
        }
      }

    case _ => s"0.1.0-SNAPSHOT"
  }
}

/** Executes the right release commands depending on if it is a snapshot version or not */
ThisProject / commands += Command.command("doRelease") { state =>
  val extractedProject = Project.extract(state)
  println(s"Publishing version: ${extractedProject.get(version)}")
  if (extractedProject.get(isSnapshot)) {
    println("Version is a snapshot. Uploading directly to Sonatype, no closing of staging repository necessary.")
    "publishSigned" :: state // :: sequences commands/tasks
  }
  else {
    println("Version is not a snapshot. Publishing to a local staging folder first to then " +
      "do bundle upload, close and release sonatype staging repository.")
    "publishSigned" :: "sonatypeBundleRelease" :: state
  }
}

/** for convenient use in CI */
val signedArtifactPaths = taskKey[String]("Newline separated list of all published artifact paths")
signedArtifactPaths := {
  signedArtifacts.value.values.mkString("\n")
}

