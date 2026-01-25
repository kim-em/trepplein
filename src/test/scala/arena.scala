package trepplein

import org.specs2.mutable._
import java.io.File
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.duration._

/**
 * Lean Kernel Arena tests.
 * https://arena.lean-lang.org/
 *
 * These tests verify trepplein against the official Lean kernel test suite.
 * Download tests with: ./scripts/download-arena-tests.sh
 */
class ArenaTest extends Specification {
  sequential

  val arenaDir = new File("/tmp/lean-arena-tests")

  def checkNdjson(path: String): Either[String, Int] = {
    val file = new File(arenaDir, path)
    if (!file.exists()) {
      return Left(s"File not found: $file (run ./scripts/download-arena-tests.sh)")
    }

    try {
      val commands = JsonExportParser.parseFile(file.getPath).toVector

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

      // Wait for all proof obligations to complete
      val result = Await.result(env.force, 300.seconds)
      result match {
        case Right(_) => Right(declCount)
        case Left(errors) => Left(errors.map(_.toString).mkString("\n"))
      }
    } catch {
      case e: Exception => Left(e.getMessage)
    }
  }

  // === Good tests (should pass) ===

  "good/tutorial/01_basicDef" in {
    checkNdjson("good/tutorial/01_basicDef.ndjson") must beRight
  }

  "good/tutorial/03_arrowType" in {
    checkNdjson("good/tutorial/03_arrowType.ndjson") must beRight
  }

  "good/tutorial/04_dependentType" in {
    checkNdjson("good/tutorial/04_dependentType.ndjson") must beRight
  }

  "good/tutorial/05_simpleLambda" in {
    checkNdjson("good/tutorial/05_simpleLambda.ndjson") must beRight
  }

  "good/tutorial/06_betaReduction" in {
    checkNdjson("good/tutorial/06_betaReduction.ndjson") must beRight
  }

  "good/tutorial/07_betaReduction2" in {
    checkNdjson("good/tutorial/07_betaReduction2.ndjson") must beRight
  }

  "good/tutorial/09_levelComp1" in {
    checkNdjson("good/tutorial/09_levelComp1.ndjson") must beRight
  }

  "good/tutorial/10_levelComp2" in {
    checkNdjson("good/tutorial/10_levelComp2.ndjson") must beRight
  }

  "good/tutorial/11_levelComp3" in {
    checkNdjson("good/tutorial/11_levelComp3.ndjson") must beRight
  }

  "good/tutorial/12_levelParams" in {
    checkNdjson("good/tutorial/12_levelParams.ndjson") must beRight
  }

  "good/tutorial/14_levelComp4" in {
    checkNdjson("good/tutorial/14_levelComp4.ndjson") must beRight
  }

  "good/tutorial/15_levelComp5" in {
    checkNdjson("good/tutorial/15_levelComp5.ndjson") must beRight
  }

  "good/tutorial/16_imax1" in {
    checkNdjson("good/tutorial/16_imax1.ndjson") must beRight
  }

  "good/tutorial/17_imax2" in {
    checkNdjson("good/tutorial/17_imax2.ndjson") must beRight
  }

  "good/tutorial/18_inferVar" in {
    checkNdjson("good/tutorial/18_inferVar.ndjson") must beRight
  }

  "good/tutorial/19_defEqLambda" in {
    checkNdjson("good/tutorial/19_defEqLambda.ndjson") must beRight
  }

  "good/tutorial/20_peano1" in {
    checkNdjson("good/tutorial/20_peano1.ndjson") must beRight
  }

  "good/tutorial/21_peano2" in {
    checkNdjson("good/tutorial/21_peano2.ndjson") must beRight
  }

  "good/tutorial/22_peano3" in {
    checkNdjson("good/tutorial/22_peano3.ndjson") must beRight
  }

  "good/init-prelude" in {
    checkNdjson("good/init-prelude.ndjson") must beRight
  }

  "good/grind-ring-5" in {
    checkNdjson("good/grind-ring-5.ndjson") must beRight
  }

  // === Bad tests (should fail) ===

  "bad/tutorial/02_badDef" in {
    checkNdjson("bad/tutorial/02_badDef.ndjson") must beLeft
  }

  "bad/tutorial/08_nonTypeType" in {
    checkNdjson("bad/tutorial/08_nonTypeType.ndjson") must beLeft
  }

  "bad/tutorial/13_tut06_bad01 (duplicate universe params)" in {
    checkNdjson("bad/tutorial/13_tut06_bad01.ndjson") must beLeft
  }

  "bad/nonPropThm (theorem with non-Prop type)" in {
    checkNdjson("bad/nonPropThm.ndjson") must beLeft
  }

  "bad/bogus1" in {
    checkNdjson("bad/bogus1.ndjson") must beLeft
  }
}
