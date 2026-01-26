package trepplein

import org.specs2.mutable._
import org.specs2.specification.core.Fragments
import java.io.File
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.duration._

/**
 * Integration test for processing the Batteries library export.
 *
 * To generate the export file, run:
 *   ./scripts/generate-batteries-export.sh
 */
class BatteriesExportTest extends Specification {
  val batteriesExportPath = "/tmp/batteries.lean4export"

  "Batteries library export" in {
    val file = new File(batteriesExportPath)
    if (!file.exists()) {
      skipped(s"Batteries export not found at $batteriesExportPath - run ./scripts/generate-batteries-export.sh")
    }

    val stream = new java.io.FileInputStream(file)
    try {
      val commands = TextExportParser.parseStream(stream).toVector

      var env: PreEnvironment = Environment.default
      var declCount = 0

      for (cmd <- commands) {
        cmd match {
          case ExportedModification(mod) =>
            val (_, newEnv) = env.addWithFuture(mod)
            env = newEnv
            declCount += 1
          case _ =>
        }
      }

      val result = Await.result(env.force, 30.minutes)
      result match {
        case Right(_) =>
          declCount must beGreaterThan(50000)
        case Left(errors) =>
          failure(s"${errors.size} errors:\n${errors.take(10).map(_.toString).mkString("\n")}")
      }
    } finally {
      stream.close()
    }
  }
}
