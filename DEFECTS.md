# Trepplein Type Checker Defects

This document catalogs known defects in trepplein's type checking, validated by comparison against three reference implementations:
- **lean4** (C++) — The official Lean 4 kernel at `/tmp/lean4/src/kernel/`
- **lean4lean** (Lean 4) — Independent checker at `/tmp/lean4lean/`
- **nanoda_lib** (Rust) — Independent checker at `/tmp/nanoda_lib/`

Each defect is marked with severity and includes specific code locations in both trepplein and the reference implementations.

---

## CRITICAL-1: `trustExports` Bypass Enabled by Default

### Trepplein Behavior
**Location:** `environment.scala:64, 113, 130`

Every `DefMod`, `TheoremMod`, and `OpaqueMod` is checked with `trustExports = true`:
```scala
def check(): Unit = {
  val tc = new TypeChecker(env, trustExports = true)  // ALWAYS TRUE
  // ...
}
```

When enabled, type mismatches can be silently accepted via bypass mechanisms (see CRITICAL-2).

### Reference Implementation Behavior

**lean4** (`type_checker.cpp:100-108`): No trust bypass exists. The `definition_safety` enum only controls whether unsafe/partial definitions can be *used*, not whether type checking occurs. All type mismatches throw `app_type_mismatch_exception`.

**lean4lean** (`TypeChecker.lean:24-36`): No trust flags. The `Methods.withFuel.WF` proof demonstrates every call maintains full type safety invariants. No code path skips verification.

**nanoda_lib** (`tc.rs:79-102`): No trust/unsafe bypass. All declarations go through `check_declar()` which calls `assert_def_eq()` on type mismatches—panics immediately, never silently accepts.

### Impact
The entire purpose of an independent type checker is undermined. Malicious exports could pass invalid proofs.

---

## CRITICAL-2: `hasBoundVariableMismatch` Bypass

**Test Status:** Not yet reproduced - simple type corruptions are correctly rejected.

### Trepplein Behavior
**Location:** `typechecker.scala:368-385`

```scala
private def hasBoundVariableMismatch(a: Expr, b: Expr): Boolean = {
  def hasLocalConst(start: Expr): Boolean = { /* tree traversal */ }
  hasLocalConst(a) || hasLocalConst(b)  // EITHER side having ANY LocalConst passes
}
```

If **either** side of a type mismatch contains **any** `LocalConst` **anywhere** in the expression tree, the mismatch is ignored when `trustExports = true`.

**Note on reproduction:** Simple type corruptions (changing a definition's declared type) are correctly rejected because the final compared expressions (declared type vs inferred type) are closed terms without `LocalConst`. The bypass only triggers when stuck computations leave `LocalConst` in the result - a more complex edge case involving recursor applications on abstract arguments that fail to reduce.

### Reference Implementation Behavior

**lean4** (`type_checker.cpp:163-176`): No such bypass. `is_def_eq()` either succeeds or throws `app_type_mismatch_exception`. There is no "allow if contains local" logic.

**lean4lean** (`IsDefEq.lean`): Full structural equality checking. The `isDefEq` function recursively compares all subterms. No shortcut for expressions containing locals.

**nanoda_lib** (`tc.rs:801-808`): `assert_def_eq()` panics on any mismatch:
```rust
if !self.def_eq(u, v) {
    panic!("failed decl name := {:?}\n\nu := {}\n\nv := {}", declar_name, u, v)
}
```

### Impact
A bypass for stuck computations. An attacker may be able to craft terms that always contain a LocalConst to evade type checking.

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
| CRITICAL-1 | Critical | `trustExports` bypass default | Open |
| CRITICAL-2 | Critical | `hasBoundVariableMismatch` | Narrowed, not fully reproduced |
| MEDIUM-2 | Medium | Mutable globals | Open |
| MEDIUM-4 | Medium | `unsafeUnchecked` flag | Open |

---

## Resolved Defects

The following defects have been fixed:

| ID | Issue | Resolution |
|----|-------|------------|
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
