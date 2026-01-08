# Trepplein Type Checker Defects

This document catalogs known defects in trepplein's type checking, validated by comparison against three reference implementations:
- **lean4** (C++) — The official Lean 4 kernel at `/tmp/lean4/src/kernel/`
- **lean4lean** (Lean 4) — Independent checker at `/tmp/lean4lean/`
- **nanoda_lib** (Rust) — Independent checker at `/tmp/nanoda_lib/`

Each defect is marked with severity and includes specific code locations in both trepplein and the reference implementations.

---

## CRITICAL-1: `trustExports` Bypass Enabled by Default

**Status:** Significantly tightened (January 2026)

### Current Behavior
**Location:** `environment.scala:64, 133, 151` and `typechecker.scala:1917-1934`

Declarations are checked with `trustExports = true`, but bypass conditions have been simplified from 11 to just 2:

```scala
val canBypass = trustExports && (
  isStuckTerm(i_) || isStuckTerm(t_) ||   // Projections on non-constructors
  hasLocalConst(t_) || hasLocalConst(i_)  // Expressions with free variables
)
```

**Analysis (Init export, ~50k declarations):**
- `isStuckTerm`: 35,287 uses - projections on opaques (e.g., `System.Platform.getNumBits`)
- `hasLocalConst`: ~4,200 uses - expressions with free variables that prevent reduction

### Removed Bypass Conditions
The following overly-permissive conditions were removed:
- `shareLocalConstants` - both sides sharing same locals
- `hasRecursorOnLocalConst` - recursor on variable
- `containsRecursor` - any recursor anywhere
- `isBareLocalConst` - either side is just a variable
- `hasStuckProjection && hasLocalConst` - stuck projection with local const

### Remaining Concern
The `hasLocalConst` bypass is still permissive - any expression with a free variable passes. This is necessary for ~4,200 declarations in Init, but could potentially be exploited.

---

## MEDIUM-2: Mutable Global State for Literal Reduction

### Trepplein Behavior
**Location:** `literal.scala:12-13`

```scala
object LiteralReduction {
  var enableNatReduction: Boolean = true
  var enableStringReduction: Boolean = true
```

These mutable global variables can be changed by any code in the process, affecting whether `Nat.add`, `Nat.mul`, etc. reduce.

### Reference Implementation Behavior

**lean4**: Literal reduction is built into the kernel with no disable flags.

**lean4lean**: No mutable state affecting reduction.

**nanoda_lib**: No mutable state affecting reduction.

### Impact
Code could disable literal reduction causing terms to fail to reduce that should, potentially causing spurious type mismatches or (with trustExports) silent acceptance of wrong results.

---

## MEDIUM-4: `unsafeUnchecked` Flag Exists

### Trepplein Behavior
**Location:** `typechecker.scala:15-16, 407`

```scala
class TypeChecker(..., val unsafeUnchecked: Boolean = false, ...) {
  def shouldCheck: Boolean = !unsafeUnchecked
  // ...
  if (shouldCheck) { checkType(a, expectedTy) }  // Skipped when unsafeUnchecked!
```

Currently only used for pretty-printing (`main.scala:17`), but the API allows instantiating a TypeChecker that skips argument checking.

### Reference Implementation Behavior

**lean4** (`type_checker.cpp:163`): Has `infer_only` mode for performance, but this is a separate code path that clearly doesn't claim to verify, not a bypass flag on the main checker.

**lean4lean/nanoda_lib**: No such flags.

### Impact
If accidentally used for actual verification, would accept invalid terms.

---

## Summary Table

| ID | Severity | Issue | Status |
|----|----------|-------|--------|
| CRITICAL-1 | Critical | `trustExports` bypass default | Tightened (11→2 conditions) |
| MEDIUM-2 | Medium | Mutable globals | Open |
| MEDIUM-4 | Medium | `unsafeUnchecked` flag | Open |

---

## Resolved Defects

The following defects have been fixed:

| ID | Issue | Resolution |
|----|-------|------------|
| CRITICAL-2 | `hasBoundVariableMismatch` bypass | Removed; now simplified to `isStuckTerm` + `hasLocalConst` only |
| CRITICAL-3 | `Level.Zero` placeholder in `inferUniverseOfType` | Now throws error instead of returning placeholder |
| HIGH-1 | No recursor well-formedness checking | Added validation in `RecursorMod.check()` |
| HIGH-2 | Proof irrelevance types not checked | `isProofIrrelevantEq` now verifies types are def-eq |
| HIGH-3 | Constructor metadata trusted | Validates numParams/numFields against type structure in `CtorMod.check()` |
| HIGH-4 | Universe level validation incomplete | Added universe param validation in `IndMod.check()` |
| HIGH-5 | `lcProof` placeholder proofs | Removed lcProof entirely; now follows nanoda_lib approach of not reducing decidability |
| MEDIUM-1 | Positivity check incomplete | Now checks for negative occurrences inside type arguments |
| MEDIUM-3 | Integer overflow in `Nat.pow` | Uses `intValueExact` with proper error handling |

Regression tests in `conformance.scala` verify that `RecursorRhsUnchecked` and `WrongUniverse` exports are correctly rejected.

---

## Validation Methodology

### Tools Used
- **nanoda_lib** (`/tmp/nanoda_lib`) - Rust implementation, requires JSON config file
- **trepplein** - Run via `sbt "run path/to/export"`

### nanoda_lib Config Template
```json
{
    "export_file_path": "/path/to/export",
    "use_stdin": false,
    "permitted_axioms": [],
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "print_success_message": true
}
```

### Validation Process
1. Create minimal export file exposing the defect
2. Test with nanoda_lib first - must REJECT (panic or error)
3. Test with trepplein - if it ACCEPTS, we have a differential bug
4. Add test to `conformance.scala` with `must beLeft` assertion

---

## Future Investigation Ideas

### Unexplored Vectors
1. **Recursor major premise manipulation** - What if we corrupt which argument is the "major premise"?
2. **Nested inductive types** - The positivity check (MEDIUM-1) may be bypassable with complex nested structures
3. **Universe constraint accumulation** - Can we construct exports where universe constraints are inconsistent but not checked?
4. **Quotient type rules** - Are `Quot.mk`, `Quot.lift`, `Quot.ind` rules validated?

### Test Cases to Create
- [ ] `NonpositiveNested` - Nested inductive that bypasses simple positivity check
- [ ] `QuotientRuleCorrupt` - Corrupted quotient type reduction rules
- [ ] `RecursorMajorWrong` - Wrong major premise index in recursor
