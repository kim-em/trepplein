#!/bin/bash
set -e

# Download Lean Kernel Arena tests
# Output: /tmp/lean-arena-tests/
#
# Usage: ./scripts/download-arena-tests.sh

ARENA_URL="https://arena.lean-lang.org/lean-arena-tests.tar.gz"
OUTPUT_DIR="/tmp/lean-arena-tests"

echo "Downloading arena tests from $ARENA_URL..."

cd /tmp
rm -rf lean-arena-tests lean-arena-tests.tar.gz

curl -L -o lean-arena-tests.tar.gz "$ARENA_URL"
tar -xzf lean-arena-tests.tar.gz

# Count tests
GOOD_COUNT=$(find "$OUTPUT_DIR/good" -name "*.ndjson" | wc -l | tr -d ' ')
BAD_COUNT=$(find "$OUTPUT_DIR/bad" -name "*.ndjson" | wc -l | tr -d ' ')

echo ""
echo "Downloaded arena tests to $OUTPUT_DIR"
echo "Good tests: $GOOD_COUNT"
echo "Bad tests: $BAD_COUNT"
