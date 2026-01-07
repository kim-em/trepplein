## trepplein: a Lean 4 type-checker

Trepplein is an independent type-checker for [Lean 4](https://lean-lang.org/). It verifies exported proof terms to provide additional trust in the Lean kernel.

### Building

Trepplein is written in Scala and requires [SBT](http://www.scala-sbt.org/) to build:

```bash
sbt compile
```

### Exporting from Lean 4

Trepplein consumes exports produced by [lean4export](https://github.com/leanprover/lean4export). Currently, you must use the [kim-em/lean4export](https://github.com/kim-em/lean4export) fork with the `fix-nondep-normalization` branch, which fixes issues with non-dependent type normalization (see [lean4export#11](https://github.com/leanprover/lean4export/pull/11)). Once that PR is merged, you can use the upstream lean4export directly.

To export a Lean 4 project:

```bash
# Clone and build lean4export (use the same toolchain as your project)
# TODO: Once PR #11 is merged, use https://github.com/leanprover/lean4export instead
git clone https://github.com/kim-em/lean4export -b fix-nondep-normalization
cd lean4export
cp /path/to/your/project/lean-toolchain .
lake build
cd ..

# Export your project (e.g., Init)
cd /path/to/your/project
lake env /path/to/lean4export/.lake/build/bin/lean4export Init > init.export
```

### Testing against Lean 4 Init

The `scripts/generate-init-export.sh` script generates an export of Lean 4's Init library using the latest nightly toolchain:

```bash
# Generate export (uses today's nightly)
./scripts/generate-init-export.sh

# Or use a specific nightly
LEAN_NIGHTLY=2026-01-07 ./scripts/generate-init-export.sh

# Run the Init test
sbt -J-Xss100m -J-Xmx8g "testOnly *InitExportTest"
```

This is also run in CI on every push.

### Running trepplein

```bash
# Check an export file
sbt "run path/to/export.txt"

# Benchmark mode (check multiple files, report timing)
sbt "run --benchmark file1.export file2.export file3.export"

# Sequential checking (single-threaded)
sbt "run --sequential path/to/export.txt"
```

### Export formats

Trepplein supports both text and NDJSON export formats. The format is auto-detected, or can be specified explicitly:

```bash
sbt "run --format text path/to/export.txt"
sbt "run --format json path/to/export.json"
```

### Other Lean 4 checkers

* [nanoda_lib](https://github.com/ammkrn/nanoda_lib) - a type-checker written in Rust
* [lean4checker](https://github.com/leanprover/lean4checker) - official checker using Lean's kernel

### Legacy

For Lean 3 support, see older versions of trepplein. This version (2.x) supports Lean 4 only.
