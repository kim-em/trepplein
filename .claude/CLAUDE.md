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

# Run on an export file
sbt "run /path/to/file.export"

# Run with increased stack for large files
sbt -J-Xss100m "run /path/to/file.export"
```

## Debugging Reduction Failures

When something doesn't reduce properly:
1. Use export analysis tools to trace the definition chain
2. Check if all intermediate definitions have reduction rules
3. Verify recursor rules are generated correctly
4. Trace the actual whnf computation to find where reduction stops
