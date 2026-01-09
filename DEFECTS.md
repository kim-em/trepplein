# Trepplein Type Checker Defects

This document catalogs known defects in trepplein's type checking, validated by comparison against three reference implementations:
- **lean4** (C++) — The official Lean 4 kernel at `/tmp/lean4/src/kernel/`
- **lean4lean** (Lean 4) — Independent checker at `/tmp/lean4lean/`
- **nanoda_lib** (Rust) — Independent checker at `/tmp/nanoda_lib/`

Each defect is marked with severity and includes specific code locations in both trepplein and the reference implementations.

---

## CRITICAL-1: `trustExports` Bypass

**Status:** Main bypass DISABLED (January 2026)

### Current Behavior
**Location:** `environment.scala:64, 133, 151` and `typechecker.scala:2287`

Declarations are checked with `trustExports = true`, but the main bypass is **currently disabled**:

```scala
val canBypass = false && trustExports && (
  isStuckTerm(i_) || isStuckTerm(t_) ||   // Projections on non-constructors
  hasLocalConst(t_) || hasLocalConst(i_)  // Expressions with free variables
)
```

The `false &&` prefix means the main bypass never triggers. This was done to investigate what actually fails.

**Note:** `trustExports` still has effect in other places:
- `isStuckTerm` checks in whnf fallbacks (lines 2478, 2515, 2518, 2722, 2737)
- `tryProofIrrelevanceStuck` for proof patterns (line 165)

### Removed Bypass Conditions
The following overly-permissive conditions were removed in earlier cleanup:
- `shareLocalConstants` - both sides sharing same locals
- `hasRecursorOnLocalConst` - recursor on variable
- `containsRecursor` - any recursor anywhere
- `isBareLocalConst` - either side is just a variable
- `hasStuckProjection && hasLocalConst` - stuck projection with local const

### Current Status
With the main bypass disabled, we need to investigate which declarations in Init actually fail and determine if they represent:
1. Missing features in the type checker
2. Legitimate bugs to fix
3. Edge cases that genuinely need some form of bypass

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
| CRITICAL-1 | Critical | `trustExports` bypass | Main bypass DISABLED; fallbacks remain |
| MEDIUM-2 | Medium | Mutable globals | Open |
| MEDIUM-4 | Medium | `unsafeUnchecked` flag | Open |

### Implementation Status

- **eagerReduce support**: IMPLEMENTED (lines 2112-2240 in typechecker.scala)
  - Detection, `withEagerReduce` mode, `fullyReduce`, aggressive whnf all present
  - Required for `native_decide` proofs

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

## Init Library Failures (January 2026)

With the main bypass disabled (`canBypass = false`), **328 declarations** fail type checking in the Init export.

### Failure Patterns

| Pattern | Count | Description |
|---------|-------|-------------|
| `PProd.0 (List.rec` | 34 | Projection on list recursor |
| `Quot.lift` | 25 | Quotient lift not reducing |
| `Bool.true ... Prod.0 (Option.rec` | 18 | Decidability not reducing to Bool.true |
| `PProd.0 (Nat.rec` | 17 | Projection on Nat recursor |
| `Fin n PProd.0 (Nat.rec` | 10 | Fin in projection context |
| Other patterns | ~224 | Various projection/recursor combinations |

### Root Causes

1. **Projections on recursors**: When a recursor is applied to an abstract argument, projections can't extract values. Example: `PProd.0 (List.rec ... xs)` where `xs` is a variable.

2. **Quotient operations**: `Quot.lift` and `Quot.mk` operations don't reduce when the quotient relation isn't concrete.

3. **Decidability not computing**: Some `ite` expressions have decidable instances that don't reduce to `Bool.true/false`, leaving the conditional unreduced.

### Affected Declarations

- BitVec operations: `divRec_succ'`, `toFin_and`, `toFin_xor`, etc.
- Fin operations: `val_mul`, `shiftLeft_val`, `induction_succ`, etc.
- Vector/Array: `pmap_*`, `attach_*`, `forIn'_*` operations
- UInt operations: `ofFin_shiftLeft_mod`, `toFin_shiftLeft`
- StateT/Monad: `instLawfulMonadLift`

### Next Steps

To make trepplein a "real" type checker without bypass:
1. Improve projection reduction to handle recursors on abstract arguments
2. Implement quotient reduction semantics
3. Ensure decidability instances properly compute

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
