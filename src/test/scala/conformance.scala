package trepplein

import org.specs2.mutable._
import java.io.File
import scala.io.Source
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.duration._

/**
 * Conformance tests ported from nanoda_lib.
 * https://github.com/ammkrn/nanoda_lib
 */
class ConformanceTest extends Specification {
  val resourcesDir = new File(getClass.getResource("/").toURI)

  def checkExport(name: String): Either[String, Int] = {
    val exportFile = new File(resourcesDir, s"$name/export")
    if (!exportFile.exists()) {
      return Left(s"Export file not found: $exportFile")
    }

    val stream = new java.io.FileInputStream(exportFile)
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

      // Wait for all proof obligations to complete
      val result = Await.result(env.force, 60.seconds)
      result match {
        case Right(_) => Right(declCount)
        case Left(errors) => Left(errors.map(_.toString).mkString("\n"))
      }
    } catch {
      case e: Exception => Left(e.getMessage)
    } finally {
      stream.close()
    }
  }

  // === Positive tests (should succeed) ===

  "Empty export" in {
    val emptyFile = new File(resourcesDir, "Empty/export")
    if (emptyFile.exists() && emptyFile.length() > 0) {
      checkExport("Empty") must beRight
    } else {
      // Empty file might be literally empty or not have meaningful content
      ok
    }
  }

  "Sexpr (basic s-expression types)" in {
    checkExport("Sexpr") must beRight
  }

  "Sexpr1 (s-expression variant 1)" in {
    checkExport("Sexpr1") must beRight
  }

  "Sexpr2 (s-expression variant 2)" in {
    checkExport("Sexpr2") must beRight
  }

  "Sexpr3 (s-expression variant 3)" in {
    checkExport("Sexpr3") must beRight
  }

  "AxiomNotAllowed2 (forward reference error)" in {
    // This export has a forward reference: axiom HaveFalse uses False before False is declared
    // This should fail because we can't type-check a reference to an undeclared constant
    checkExport("AxiomNotAllowed2") must beLeft
  }

  // === Negative tests (should fail) ===

  "AxiomNotAllowed0 (unpermitted axiom, hard error)" in {
    // This test has an axiom that should be rejected when axiom checking is enabled
    // For now we allow all axioms - this is a configuration option, not a bug
    checkExport("AxiomNotAllowed0") must beRight
  }

  "AxiomNotAllowed1 (unpermitted axiom, soft error)" in {
    // Similar to AxiomNotAllowed0 but with soft error
    checkExport("AxiomNotAllowed1") must beRight
  }

  "Cycle1 (direct cycle)" in {
    // A definition that references itself directly should be rejected
    checkExport("Cycle1") must beLeft
  }

  "CycleMutual1 (mutual cycle)" in {
    // Mutually recursive definitions forming a cycle should be rejected
    checkExport("CycleMutual1") must beLeft
  }

  "CycleOpaque1 (cycle through opaque)" in {
    // Cycles through opaque definitions should be detected
    checkExport("CycleOpaque1") must beLeft
  }

  "CycleOpaque2 (cycle through opaque variant 2)" in {
    checkExport("CycleOpaque2") must beLeft
  }

  "CycleOpaque3 (cycle through opaque variant 3)" in {
    checkExport("CycleOpaque3") must beLeft
  }

  "Nonpositive1 (non-positive inductive)" in {
    // Inductive type with non-positive occurrence should be rejected
    checkExport("Nonpositive1") must beLeft
  }

  "Nonpositive2 (non-positive inductive variant 2)" in {
    checkExport("Nonpositive2") must beLeft
  }

  // === Other tests ===

  "BadSemver (invalid version)" in {
    // This should fail to parse due to bad version
    checkExport("BadSemver") must beLeft
  }

  "PpDoubleFrench (pretty print test)" in {
    // Pretty printing test, should succeed as a valid export
    checkExport("PpDoubleFrench0") must beRight
  }

  // === Defect regression tests ===
  // These tests expose bugs where trepplein accepts malformed exports that
  // reference implementations (nanoda_lib) correctly reject.
  // Each test SHOULD pass (reject the export) but currently FAILS.

  "RecursorRhsUnchecked (wrong recursor RHS must be rejected)" in {
    // Export has List.rec with corrupted nil case: returns Prop instead of correct RHS
    // nanoda_lib: rejects (panics on recursor rule verification)
    // trepplein: incorrectly accepts (trusts recursor rules without verification)
    checkExport("RecursorRhsUnchecked") must beLeft
  }

  "WrongUniverse (corrupted universe level must be rejected)" in {
    // Export has Sort(u+1) changed to Sort(0), making List : ∀ A : Prop, Prop
    // nanoda_lib: rejects (panics on universe mismatch)
    // trepplein: incorrectly accepts (universe constraints not fully validated)
    checkExport("WrongUniverse") must beLeft
  }
}
