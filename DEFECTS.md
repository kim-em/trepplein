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

## HIGH-3: Constructor Metadata Trusted Without Validation

### Trepplein Behavior
**Location:** `environment.scala:173-185`

```scala
final case class CtorMod(name: Name, univParams: Vector[Level.Param], ty: Expr,
    inductName: Name, cidx: Int, numParams: Int, numFields: Int) extends Modification {
  def compile(env: PreEnvironment): CompiledModification = new CompiledModification {
    val decl = Declaration(name, univParams, ty, builtin = true)
    def check(): Unit = {
      decl.check(env)
      checkStrictPositivity(inductName, ty, numParams)
    }
    // numParams and numFields are TRUSTED from export, not validated
```

The `numParams` and `numFields` values are taken directly from the export without verifying they match the actual structure of `ty`. These values affect projection type inference (`typechecker.scala:506`).

### Reference Implementation Behavior

**lean4** (`inductive.cpp:413-454`): Constructor validation counts foralls in the type, validates each parameter matches the inductive type's parameter, and computes numFields from actual structure.

**lean4lean** (`Inductive/Add.lean:239-250`):
```lean
let arity := arity 0 type  -- Computed from actual forall structure
numFields := assert! arity ≥ stats.params.size; arity - stats.params.size
```

**nanoda_lib** (`inductive.rs:101-119`):
```rust
let num_fields = self.pi_telescope_size(ctor.ty) - num_params;  // COMPUTED from type
```

### Impact
Wrong metadata could cause projection type inference to extract wrong fields or crash.

---

## HIGH-5: `lcProof` Placeholder Used for Native Computation Proofs

### Trepplein Behavior
**Location:** `typechecker.scala:846, 1196, 1284, 1358` and `literal.scala:460-471`

Trepplein uses a magic `lcProof` constant as a placeholder for proof terms in native computations:

```scala
// environment.scala - lcProof is declared as a built-in axiom
val lcProofName = Name.mkStr(Name.Anon, "lcProof")
val lcProofTy = Pi(Binding(_, Sort(uParam), Implicit), Var(0))  // {α : Sort u} → α
val lcProofDecl = Declaration(lcProofName, Vector(uParam), lcProofTy, builtin = true)
```

This `lcProof : ∀ α, α` can prove any proposition. It's used when:
1. **Decidability reduction** (`Nat.decLt`, `Nat.decLe`, `Nat.decEq`) - produces `Decidable.isTrue lcProof` instead of proper proof terms
2. **Fin.mk construction** - uses `lcProof` for the `val < n` bound proof
3. **Subtype.mk construction** - uses `lcProof` for the predicate proof
4. **BitVec.ofNat** - uses `lcProof` through Fin.mk

### Reference Implementation Behavior

**nanoda_lib** (`tc.rs:323-343`):
- Does NOT reduce `Nat.decLt`/`Nat.decLe`/`Nat.decEq` at all
- Only reduces Boolean comparisons (`Nat.beq`, `Nat.ble`) to `Bool.true`/`Bool.false`
- Does NOT have any "sorry" or placeholder proof constants
- No special handling for Fin.mk, Subtype.mk, or BitVec

**lean4** (`type_checker.cpp`, `inductive.cpp`):
- Uses **proof-producing lemmas** like `eq_of_beq_eq_true`, `Nat.le_of_ble_eq_true`
- When `Nat.decEq 5 5` reduces, it produces `Decidable.isTrue (eq_of_beq_eq_true rfl)`
- The lemmas convert Boolean computation results to actual logical proofs
- Final terms contain fully-realized proof terms, not placeholders
- The kernel has native reduction for `Nat.beq`/`Nat.ble`, and the proof lemmas do the rest

### How Lean 4 Actually Works

```lean
@[reducible, extern "lean_nat_dec_eq"]
protected def Nat.decEq (n m : @& Nat) : Decidable (Eq n m) :=
  match h:beq n m with
  | true  => isTrue (eq_of_beq_eq_true h)   -- Real proof!
  | false => isFalse (ne_of_beq_eq_false h) -- Real proof!
```

The kernel:
1. Reduces `beq n m` using native arithmetic
2. The match produces `isTrue (eq_of_beq_eq_true h)` where `h : beq n m = true`
3. `eq_of_beq_eq_true` reduces `h` (which is `rfl` since beq reduced to true) to produce `rfl : n = m`
4. Final result: `isTrue rfl` - a proper proof term

### Impact

The `lcProof` approach means trepplein:
- Generates proof terms that don't exist in the export and are semantically invalid
- Bypasses the fundamental property that proofs must be constructible
- Requires special handling in `isProofIrrelevantEq` and `checkType` to accept these fake proofs

This is a form of "cheating" that neither nanoda_lib nor the Lean 4 kernel does. The correct fix would be to either:
1. **Not reduce decidability** (like nanoda_lib) - simpler, loses some reduction capability
2. **Implement proof-producing lemmas** (like Lean 4) - more work, fully correct

---

## MEDIUM-1: Strict Positivity Check Incomplete

### Trepplein Behavior
**Location:** `inductive.scala:61-80`

```scala
def checkPositive(ty: Expr, isArgType: Boolean): Unit = ty match {
  case Pi(Binding(_, dom, _), body) =>
    if (isArgType) {
      if (occursIn(dom, indName)) {
        throw new IllegalArgumentException(...)
      }
      checkPositive(body, isArgType = true)
    } else {
      checkPositive(dom, isArgType = true)
      checkPositive(body, isArgType = false)
    }
  case _ => ()  // Base case: not a Pi, no further checking
}
```

The check only looks for direct occurrences of the inductive name in domains of Pi types. It doesn't handle:
- Nested inductives (`List (Tree A)` where `Tree` uses `List`)
- The inductive appearing inside type applications
- Complex negative positions through type aliases

### Reference Implementation Behavior

**lean4** (`inductive.cpp:392-409`): Three-case analysis with `has_ind_occ()` that traverses all subterms, `is_valid_ind_app()` that validates the exact form of recursive occurrences.

**lean4lean** (`Inductive/Add.lean:181-196`): `hasIndOcc` traverses entire expression, `checkPositivity` validates all recursive occurrences match exact inductive type form.

**nanoda_lib** (`inductive.rs:659-679`): Uses `has_ind_occ()` for full traversal, panics on any negative occurrence, validates all positive occurrences via `which_valid_ind_app()`.

### Impact
A carefully crafted non-strictly-positive type could slip through, enabling non-termination or inconsistency.

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
| HIGH-3 | High | Constructor metadata trusted | Open |
| HIGH-5 | High | `lcProof` placeholder proofs | Open |
| MEDIUM-1 | Medium | Positivity incomplete | Open |
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
| HIGH-4 | Universe level validation incomplete | Added universe param validation in `IndMod.check()` |
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
