#!/bin/bash
set -e

# Generate Init export from Lean 4 nightly
# Output: /tmp/init.lean4export
#
# Usage:
#   ./scripts/generate-init-export.sh              # Uses today's nightly
#   LEAN_NIGHTLY=2026-01-07 ./scripts/generate-init-export.sh  # Uses specific date

# Get nightly date (today if not set)
NIGHTLY=${LEAN_NIGHTLY:-$(date +%Y-%m-%d)}
TOOLCHAIN="leanprover/lean4-nightly:nightly-$NIGHTLY"

echo "Using toolchain: $TOOLCHAIN"

# Work in /tmp
WORKDIR=/tmp/lean4-export-$$
mkdir -p "$WORKDIR"
cd "$WORKDIR"

cleanup() {
    rm -rf "$WORKDIR"
}
trap cleanup EXIT

# 1. Create a simple project that imports Init
echo "Creating test project..."
mkdir test-project
cd test-project
cat > lakefile.toml << 'EOF'
name = "test"
version = "0.1.0"
defaultTargets = ["test"]

[[lean_lib]]
name = "test"
EOF
echo "$TOOLCHAIN" > lean-toolchain
cat > test.lean << 'EOF'
import Init
EOF

# 2. Build to download toolchain and get Init
echo "Building project (downloads toolchain if needed)..."
lake build

# 3. Clone lean4export fork with nonDep fix
echo "Cloning lean4export fork..."
cd "$WORKDIR"
git clone -b fix-nondep-normalization https://github.com/kim-em/lean4export.git lean4export
cd lean4export
echo "$TOOLCHAIN" > lean-toolchain
lake build

# 4. Export Init
echo "Exporting Init..."
cd "$WORKDIR/test-project"
lake env "$WORKDIR/lean4export/.lake/build/bin/lean4export" Init > /tmp/init.lean4export

LINES=$(wc -l < /tmp/init.lean4export)
echo ""
echo "Generated /tmp/init.lean4export ($LINES lines)"
echo "Toolchain: $TOOLCHAIN"
