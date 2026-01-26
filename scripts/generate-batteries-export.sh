#!/bin/bash
set -e

# Generate Batteries library export
# Output: /tmp/batteries.lean4export
#
# Batteries is the community standard library extension.
# Uses the toolchain pinned by Batteries (currently v4.27.0).

echo "Generating Batteries export..."

# Work in /tmp
WORKDIR=/tmp/batteries-export-$$
mkdir -p "$WORKDIR"
cd "$WORKDIR"

cleanup() {
    rm -rf "$WORKDIR"
}
trap cleanup EXIT

# 1. Create a project that imports Batteries
echo "Creating test project..."
mkdir test-project
cd test-project
cat > lakefile.lean << 'EOF'
import Lake
open Lake DSL

package batteries_test

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_lib BatteriesTest
EOF

cat > BatteriesTest.lean << 'EOF'
import Batteries
EOF

# Use whatever toolchain Batteries pins
lake update

# 2. Build the project
echo "Building project (this downloads Batteries)..."
lake build

# Get the toolchain that was used
TOOLCHAIN=$(cat lean-toolchain)
echo "Using toolchain: $TOOLCHAIN"

# 3. Clone lean4export with matching toolchain
echo "Cloning lean4export..."
cd "$WORKDIR"
if [ ! -d lean4export ]; then
    git clone -b fix-nondep-normalization https://github.com/kim-em/lean4export.git lean4export
fi
cd lean4export
echo "$TOOLCHAIN" > lean-toolchain
lake build

# 4. Export Batteries
echo "Exporting Batteries..."
cd "$WORKDIR/test-project"
lake env "$WORKDIR/lean4export/.lake/build/bin/lean4export" Batteries > /tmp/batteries.lean4export

LINES=$(wc -l < /tmp/batteries.lean4export)
echo ""
echo "Generated /tmp/batteries.lean4export ($LINES lines)"
echo "Toolchain: $TOOLCHAIN"
