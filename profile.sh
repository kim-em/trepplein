#!/bin/bash
#
# Profile trepplein using Java Flight Recorder (JFR)
#
# Usage: ./profile.sh [export_file] [duration_seconds]
#
# This generates:
#   - profile.jfr: Full JFR recording
#   - profile-cpu.txt: CPU hotspots summary
#   - profile-alloc.txt: Allocation hotspots summary
#

set -e

TREPPLEIN_DIR="$(cd "$(dirname "$0")" && pwd)"
EXPORT_FILE="${1:-/tmp/init-200k.export}"
DURATION="${2:-120}"
RESULTS_DIR="/tmp/trepplein-profile"

mkdir -p "$RESULTS_DIR"

if [ ! -f "$EXPORT_FILE" ]; then
    echo "Export file not found: $EXPORT_FILE"
    echo "Please provide an export file as the first argument"
    exit 1
fi

echo "=============================================="
echo "Trepplein Profiling"
echo "=============================================="
echo ""
echo "Export file: $EXPORT_FILE"
echo "Duration limit: ${DURATION}s"
echo "Results directory: $RESULTS_DIR"
echo ""

# Build first
echo "Building trepplein..."
cd "$TREPPLEIN_DIR"
sbt -J-Xmx4g compile 2>&1 | tail -3

# JFR settings for detailed profiling
JFR_SETTINGS="settings=profile"

# Run with JFR profiling
echo ""
echo "Running with JFR profiling..."
echo ""

# Create a simple Scala runner that we can profile
cat > "$RESULTS_DIR/ProfileRunner.scala" << 'SCALA'
import trepplein._
import java.io.FileInputStream
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.duration._

object ProfileRunner {
  def main(args: Array[String]): Unit = {
    val exportFile = args(0)
    println(s"Processing: $exportFile")

    val startTime = System.currentTimeMillis()

    val stream = new FileInputStream(exportFile)
    try {
      val commands = TextExportParser.parseStream(stream).toVector
      println(s"Parsed ${commands.size} commands in ${System.currentTimeMillis() - startTime}ms")

      val checkStart = System.currentTimeMillis()
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

      println(s"Added $declCount declarations in ${System.currentTimeMillis() - checkStart}ms")

      // Wait for all proof obligations
      val waitStart = System.currentTimeMillis()
      val result = Await.result(env.force, 30.minutes)

      result match {
        case Right(_) =>
          println(s"All checks passed in ${System.currentTimeMillis() - waitStart}ms")
        case Left(errors) =>
          println(s"Completed with ${errors.size} errors in ${System.currentTimeMillis() - waitStart}ms")
          errors.take(5).foreach(e => println(s"  - $e"))
      }

      val totalTime = System.currentTimeMillis() - startTime
      println(s"\nTotal time: ${totalTime}ms")
    } finally {
      stream.close()
    }
  }
}
SCALA

# Run sbt with JFR enabled
echo "Starting JFR recording..."
sbt -J-Xmx8g -J-Xss30m \
    -J-XX:+UnlockDiagnosticVMOptions \
    -J-XX:+DebugNonSafepoints \
    "-J-XX:StartFlightRecording=filename=$RESULTS_DIR/profile.jfr,dumponexit=true,$JFR_SETTINGS" \
    "runMain trepplein.main $EXPORT_FILE" 2>&1 | tee "$RESULTS_DIR/run-output.txt"

echo ""
echo "=============================================="
echo "Profiling Complete"
echo "=============================================="
echo ""
echo "JFR recording saved to: $RESULTS_DIR/profile.jfr"
echo ""
echo "To analyze the recording:"
echo "  1. Open with JDK Mission Control: jmc $RESULTS_DIR/profile.jfr"
echo "  2. Or use jfr command-line tool:"
echo "     jfr summary $RESULTS_DIR/profile.jfr"
echo "     jfr print --events jdk.ExecutionSample $RESULTS_DIR/profile.jfr | head -100"
echo ""

# Try to generate text summaries if jfr tool is available
if command -v jfr &> /dev/null; then
    echo "Generating summaries..."
    jfr summary "$RESULTS_DIR/profile.jfr" > "$RESULTS_DIR/profile-summary.txt" 2>&1 || true
    echo "Summary saved to: $RESULTS_DIR/profile-summary.txt"
fi
