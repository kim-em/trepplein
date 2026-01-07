#!/bin/bash
#
# Benchmark script for comparing trepplein and nanoda performance
# on Lean 4 export files.
#
# Usage: ./benchmark.sh [export_file]
#
# This script will automatically:
#   1. Clone and build nanoda_lib if not present
#   2. Clone and build lean4export if not present
#   3. Generate an Init export if no export file is specified
#   4. Run benchmarks comparing trepplein vs nanoda
#

set -e

# Configuration
TREPPLEIN_DIR="$(cd "$(dirname "$0")" && pwd)"
DEPS_DIR="$TREPPLEIN_DIR/.deps"
NANODA_DIR="$DEPS_DIR/nanoda_lib"
LEAN4EXPORT_DIR="$DEPS_DIR/lean4export"
NANODA_BIN="$NANODA_DIR/target/release/nanoda_bin"
LEAN4EXPORT_BIN="$LEAN4EXPORT_DIR/.lake/build/bin/lean4export"
RESULTS_DIR="/tmp/benchmark_results"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo "=============================================="
echo "Lean 4 Type Checker Benchmark"
echo "=============================================="
echo ""

# Create dependencies directory
mkdir -p "$DEPS_DIR"
mkdir -p "$RESULTS_DIR"

# Function to install nanoda_lib
install_nanoda() {
    echo -e "${BLUE}Installing nanoda_lib...${NC}"
    if [ ! -d "$NANODA_DIR" ]; then
        git clone https://github.com/ammkrn/nanoda_lib.git "$NANODA_DIR"
    fi
    cd "$NANODA_DIR"
    git pull --ff-only 2>/dev/null || true
    cargo build --release
    echo -e "${GREEN}nanoda_lib installed${NC}"
}

# Function to install lean4export
install_lean4export() {
    echo -e "${BLUE}Installing lean4export...${NC}"
    if [ ! -d "$LEAN4EXPORT_DIR" ]; then
        # Use kim-em fork with nonDep fix until PR #11 is merged
        git clone -b fix-nondep-normalization https://github.com/kim-em/lean4export.git "$LEAN4EXPORT_DIR"
    fi
    cd "$LEAN4EXPORT_DIR"
    git pull --ff-only 2>/dev/null || true
    lake build
    echo -e "${GREEN}lean4export installed${NC}"
}

# Check and install dependencies
if [ ! -f "$NANODA_BIN" ]; then
    install_nanoda
fi

if [ ! -f "$LEAN4EXPORT_BIN" ]; then
    install_lean4export
fi

# Determine export file
EXPORT_FILE="${1:-}"

if [ -z "$EXPORT_FILE" ]; then
    # Try to find an existing export file
    if [ -f "/tmp/init.lean4export" ]; then
        EXPORT_FILE="/tmp/init.lean4export"
        echo "Using existing export: $EXPORT_FILE"
    else
        echo -e "${YELLOW}No export file specified and none found.${NC}"
        echo ""
        echo "To generate an export file, run:"
        echo "  ./scripts/generate-init-export.sh"
        echo ""
        echo "Then run this script again with:"
        echo "  $0 /tmp/init.lean4export"
        exit 1
    fi
fi

if [ ! -f "$EXPORT_FILE" ]; then
    echo -e "${RED}Error: Export file not found: $EXPORT_FILE${NC}"
    exit 1
fi

echo ""
echo "Export file: $EXPORT_FILE"
echo "Export size: $(wc -l < "$EXPORT_FILE" 2>/dev/null || echo "N/A") lines"
echo ""

# Build trepplein
echo -e "${BLUE}Building trepplein...${NC}"
cd "$TREPPLEIN_DIR"
sbt -J-Xmx8g compile 2>&1 | tail -3

echo ""
echo "=============================================="
echo "Running Benchmarks"
echo "=============================================="

# Benchmark trepplein
echo ""
echo -e "${YELLOW}Benchmarking trepplein...${NC}"
cd "$TREPPLEIN_DIR"

TREPPLEIN_START=$(date +%s.%N)
TREPPLEIN_OUTPUT=$(sbt -J-Xmx8g "runMain trepplein.main $EXPORT_FILE" 2>&1)
TREPPLEIN_END=$(date +%s.%N)
TREPPLEIN_TIME=$(echo "$TREPPLEIN_END - $TREPPLEIN_START" | bc)
TREPPLEIN_EXIT=$?

# Count errors in trepplein output
TREPPLEIN_ERRORS=$(echo "$TREPPLEIN_OUTPUT" | grep -c "wrong type\|not a function\|requirement failed" 2>/dev/null || echo "0")

echo "$TREPPLEIN_OUTPUT" > "$RESULTS_DIR/trepplein_output.txt"

if [ $TREPPLEIN_EXIT -eq 0 ] || [ "$TREPPLEIN_ERRORS" -lt 10 ]; then
    echo -e "${GREEN}trepplein completed in ${TREPPLEIN_TIME}s with $TREPPLEIN_ERRORS errors${NC}"
else
    echo -e "${RED}trepplein failed with exit code $TREPPLEIN_EXIT${NC}"
    echo "Output saved to: $RESULTS_DIR/trepplein_output.txt"
fi

# Benchmark nanoda
NANODA_TIME="N/A"
NANODA_ERRORS="N/A"

if [ -f "$NANODA_BIN" ]; then
    echo ""
    echo -e "${YELLOW}Benchmarking nanoda...${NC}"

    # Create config file for nanoda
    CONFIG_FILE="$RESULTS_DIR/nanoda_config.json"
    cat > "$CONFIG_FILE" << EOF
{
    "export_file_path": "$EXPORT_FILE",
    "print_success_message": false
}
EOF

    cd "$NANODA_DIR"
    NANODA_START=$(date +%s.%N)
    NANODA_OUTPUT=$("$NANODA_BIN" "$CONFIG_FILE" 2>&1) || true
    NANODA_END=$(date +%s.%N)
    NANODA_TIME=$(echo "$NANODA_END - $NANODA_START" | bc)
    NANODA_EXIT=$?

    echo "$NANODA_OUTPUT" > "$RESULTS_DIR/nanoda_output.txt"

    if [ $NANODA_EXIT -eq 0 ]; then
        echo -e "${GREEN}nanoda completed in ${NANODA_TIME}s${NC}"
        NANODA_ERRORS=0
    else
        # Check if it's an actual error or just warnings
        if echo "$NANODA_OUTPUT" | grep -q "panic\|error"; then
            echo -e "${RED}nanoda failed${NC}"
            NANODA_ERRORS="failed"
            echo "Output saved to: $RESULTS_DIR/nanoda_output.txt"
        else
            echo -e "${GREEN}nanoda completed in ${NANODA_TIME}s${NC}"
            NANODA_ERRORS=0
        fi
    fi
else
    echo ""
    echo -e "${YELLOW}Skipping nanoda (binary not found)${NC}"
fi

# Print summary
echo ""
echo "=============================================="
echo "Summary"
echo "=============================================="
echo ""
printf "%-15s %15s %15s\n" "Checker" "Time (s)" "Errors"
printf "%-15s %15s %15s\n" "--------" "--------" "------"
printf "%-15s %15.2f %15s\n" "trepplein" "$TREPPLEIN_TIME" "$TREPPLEIN_ERRORS"
if [ "$NANODA_TIME" != "N/A" ]; then
    printf "%-15s %15.2f %15s\n" "nanoda" "$NANODA_TIME" "$NANODA_ERRORS"
fi
echo ""
echo "Detailed output saved to: $RESULTS_DIR/"
echo ""

# Calculate speedup if both ran
if [ "$NANODA_TIME" != "N/A" ] && [ "$NANODA_ERRORS" != "failed" ]; then
    SPEEDUP=$(echo "scale=2; $NANODA_TIME / $TREPPLEIN_TIME" | bc 2>/dev/null || echo "N/A")
    if [ "$SPEEDUP" != "N/A" ]; then
        echo "Relative performance: trepplein is ${SPEEDUP}x compared to nanoda"
    fi
fi
