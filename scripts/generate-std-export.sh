#!/bin/bash
set -e

# Generate Std library export from Lean 4
# Output: /tmp/std.lean4export
#
# The Std library is the standard library in the lean4 repo itself.
# We use v4.27.0 toolchain (compatible with Batteries).

TOOLCHAIN="leanprover/lean4:v4.27.0"

echo "Using toolchain: $TOOLCHAIN"

# Work in /tmp
WORKDIR=/tmp/std-export-$$
mkdir -p "$WORKDIR"
cd "$WORKDIR"

cleanup() {
    rm -rf "$WORKDIR"
}
trap cleanup EXIT

# 1. Create a simple project that imports Std
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
import Std
EOF

# 2. Build the project
echo "Building project (this downloads Std)..."
lake build

# 3. Clone lean4export
echo "Cloning lean4export..."
cd "$WORKDIR"
if [ ! -d lean4export ]; then
    git clone -b fix-nondep-normalization https://github.com/kim-em/lean4export.git lean4export
fi
cd lean4export
echo "$TOOLCHAIN" > lean-toolchain
lake build

# 4. Export Std
echo "Exporting Std..."
cd "$WORKDIR/test-project"
lake env "$WORKDIR/lean4export/.lake/build/bin/lean4export" Std > /tmp/std.lean4export

LINES=$(wc -l < /tmp/std.lean4export)
echo ""
echo "Generated /tmp/std.lean4export ($LINES lines)"
echo "Toolchain: $TOOLCHAIN"
