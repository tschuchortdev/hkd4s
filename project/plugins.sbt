addSbtPlugin("org.jetbrains.scala" % "sbt-ide-settings" % "1.1.2")
addSbtPlugin("org.xerial.sbt" % "sbt-sonatype" % "3.9.21")
addSbtPlugin("com.github.sbt" % "sbt-pgp" % "2.2.1")
addSbtPlugin("nl.gn0s1s" % "sbt-dotenv" % "3.0.0")

// Uses Aether to resolve maven dependencies (might be useful for resolving SNAPSHOTs) and generates the
// maven-metadata.xml correctly, which is needed by tooling like ScalaSteward. sbt-aether-deploy would be an alternative
// with better logging that only changes deployment, not dependency resolution, but unfortunately does not work with sbt-sonatype
addSbtPlugin("org.scala-sbt" % "sbt-maven-resolver" % "0.1.0")

addSbtPlugin("com.github.sbt" % "sbt-dynver" % "5.0.1")