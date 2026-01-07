# Trepplein - Independent Type Checker for Lean 4

## Project Goals

Trepplein is an **independent type checker** for Lean 4's kernel. Its purpose is to provide a fully reliable, alternative implementation that can verify Lean 4 proofs without trusting Lean's own kernel.

### Core Principles

1. **No Cheating**: Every declaration must be verified correctly according to the type theory. If something doesn't type-check, we must fix the actual reduction/inference logic, NOT add workarounds or special cases to skip failures.

2. **Independent Implementation**: The value of trepplein is that it's a separate implementation. If we add hacks to make things pass that shouldn't, we lose the security guarantees.

3. **Full Kernel Coverage**: We must implement all kernel features:
   - Definitional equality with proper reduction
   - Universe polymorphism
   - Inductive types and recursors
   - Quotient types
   - Proof irrelevance
   - **Decidability-based computation** (ite must actually reduce!)

### Current Status

The checker handles most of Lean 4's Init library (~50k declarations), but there are still failures related to:
- `ite` expressions not reducing when decidable instances should compute
- This requires the full reduction chain: ite → casesOn → rec → decidable instance → constructor

### What NOT To Do

- **Never** add pattern-matching workarounds for specific failure cases
- **Never** skip type checking based on the name of a declaration
- **Never** trust that something is correct without verifying it
- The `trustExports` flag should only affect how we handle genuinely stuck terms (like projections on variables), not computational failures

### CRITICAL: No "Trust It Works" Optimizations

**NEVER implement an optimization that assumes a computation would succeed without actually performing it.**

This includes:
- Trusting that `native_decide` proofs are correct without reducing them
- Trusting that `eagerReduce` computations would produce `Bool.true`
- Skipping expensive computations because "Lean already verified it"
- Any form of "if the proof has this shape, assume it's valid"

The ENTIRE POINT of an independent type checker is to independently verify. If verification is too slow, the correct responses are:
1. **Optimize the reduction engine** (better algorithms, native Nat ops, etc.)
2. **Accept that some proofs take time** to verify
3. **Report the limitation** to the user

The WRONG response is to pretend verification happened when it didn't. This defeats the security purpose of the project.

**If you find yourself writing code that "trusts" something without verifying it, STOP and reconsider.**

### Export Format

Lean 4 exports use a text format with indexed references. Key commands:
- `#NS`, `#NI` - Names (string, numeric)
- `#EV`, `#ES`, `#EC`, `#EA`, `#EL`, `#EP` - Expressions
- `#DEF`, `#THM`, `#AX`, `#IND`, `#CTOR`, `#REC`, `#QUOT` - Declarations
- `#RR` - Recursor rules

Use the export analysis tools in `.claude/skills/` when investigating issues.

## Building and Testing

```bash
# Compile
sbt compile

# Run on an export file (RECOMMENDED - stops on error!)
./run-trepplein.sh /path/to/file.export

# Run with increased stack for large files
sbt -J-Xss100m --error "run /path/to/file.export"
```

### Using run-trepplein.sh

The `run-trepplein.sh` wrapper script is the **preferred** way to run trepplein because:
- It automatically kills sbt when errors (StackOverflowError, etc.) are detected
- It limits output to avoid flooding the terminal
- It cleans up properly

```bash
# Basic usage
./run-trepplein.sh /tmp/init.export

# With custom line limit (default 100)
./run-trepplein.sh /tmp/init.export 200
```

**IMPORTANT**: If you encounter issues with sbt not stopping on errors, update `run-trepplein.sh` to handle the new error pattern, and update this documentation.

### Raw sbt (use sparingly)

If you must use sbt directly, note that `sbt --error` only controls log verbosity, NOT error handling. Errors from forked processes cause sbt to continue running. Workarounds:
- Use `timeout 30 sbt --error "run ..."` to force a time limit
- Pipe through `| head -N` to limit output

## Debugging Reduction Failures

When something doesn't reduce properly:
1. Use export analysis tools to trace the definition chain
2. Check if all intermediate definitions have reduction rules
3. Verify recursor rules are generated correctly
4. Trace the actual whnf computation to find where reduction stops

## Reference Type Checkers

### nanoda_lib (Rust)
An independent Lean 4 type checker. Use for validating that malformed exports are correctly rejected.

```bash
# Clone and build
cd /tmp && git clone https://github.com/ammkrn/nanoda_lib.git
cd nanoda_lib && cargo build --release

# nanoda_lib requires a JSON config file, not direct export path
cat > /tmp/check_config.json << 'EOF'
{
    "export_file_path": "/absolute/path/to/export",
    "use_stdin": false,
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "print_success_message": true
}
EOF

/tmp/nanoda_lib/target/release/nanoda_bin /tmp/check_config.json
```

### lean4lean (Lean 4)
Independent checker written in Lean 4 itself. Located at `/tmp/lean4lean`.

### lean4export
Tool to generate export files from Lean 4 modules.

```bash
# Clone and build
cd /tmp && git clone https://github.com/leanprover/lean4export.git
cd lean4export && lake build

# Export a module (must be in LEAN_PATH or core library)
lake exe lean4export ModuleName > output.export

# Include unsafe declarations (useful for negative tests)
lake exe lean4export --export-unsafe ModuleName > output.export
```

**Known issue**: For mathlib4, use the fork with leanprover/lean4export#11 applied (fixes nonDep normalization).

**Note**: lean4export requires modules to be compiled first. For minimal test exports:
1. Use `prelude` keyword for minimal dependencies
2. The existing test resources in `src/test/resources/` were generated from nanoda_lib's test suite
3. For custom exports, it may be easier to hand-craft small exports based on existing examples

### Export Format Quick Reference

```
# Version
2.0.0

# Names (index #NS parent string) or (index #NI parent number)
1 #NS 0 Foo        # name 1 = "Foo"
2 #NS 1 bar        # name 2 = "Foo.bar"

# Levels (index #Ux ...)
1 #UP 3            # level 1 = Param(name 3)
2 #US 1            # level 2 = Succ(level 1)

# Expressions (index #Ex ...)
0 #ES 0            # expr 0 = Sort(level 0) = Prop
1 #EC 1            # expr 1 = Const(name 1, no levels)
2 #EA 1 0          # expr 2 = App(expr 1, expr 0)
3 #EL #BD 2 0 1    # expr 3 = Lam(name 2, expr 0, expr 1)
4 #EP #BD 2 0 1    # expr 4 = Pi(name 2, expr 0, expr 1)
5 #EV 0            # expr 5 = Var(0)

# Declarations
#IND name type isRefl isRec numNested numParams numIndices numInds indNames... numCtors ctorNames... uparams...
#CTOR name type inductName cidx numParams numFields uparams...
#REC name type numInds indNames... numParams numIndices numMotives numMinors numRules ruleIdxs... isK uparams...
#DEF name type value hints uparams...
#THM name type value uparams...
#AX name type uparams...
```
