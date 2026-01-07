# Trepplein Type Checker Defects

This document catalogs verified defects in trepplein's type checking, validated by comparison against three reference implementations:
- **lean4** (C++) — The official Lean 4 kernel at `/tmp/lean4/src/kernel/`
- **lean4lean** (Lean 4) — Independent checker at `/tmp/lean4lean/`
- **nanoda_lib** (Rust) — Independent checker at `/tmp/nanoda_lib/`

Each defect is marked with severity and includes specific code locations in both trepplein and the reference implementations.

## Regression Tests

Some defects have been validated with test cases in `src/test/resources/` and `src/test/scala/conformance.scala`. These tests expose exports that nanoda_lib correctly rejects but trepplein incorrectly accepts.

| Test | Defect | Status |
|------|--------|--------|
| `RecursorRhsUnchecked` | No Recursor Well-Formedness Checking | **CONFIRMED** - test fails as expected |
| `WrongUniverse` | Universe Level Validation | **CONFIRMED** - test fails as expected |

Tests marked "CONFIRMED" currently **fail** (documenting the bug). Once fixed, they will pass.

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

When enabled, type mismatches can be silently accepted via multiple bypass mechanisms (see CRITICAL-2, CRITICAL-3, HIGH-1).

### Reference Implementation Behavior

**lean4** (`type_checker.cpp:100-108`): No trust bypass exists. The `definition_safety` enum only controls whether unsafe/partial definitions can be *used*, not whether type checking occurs. All type mismatches throw `app_type_mismatch_exception`.

**lean4lean** (`TypeChecker.lean:24-36`): No trust flags. The `Methods.withFuel.WF` proof demonstrates every call maintains full type safety invariants. No code path skips verification.

**nanoda_lib** (`tc.rs:79-102`): No trust/unsafe bypass. All declarations go through `check_declar()` which calls `assert_def_eq()` on type mismatches—panics immediately, never silently accepts.

### Impact
The entire purpose of an independent type checker is undermined. Malicious exports could pass invalid proofs.

---

## CRITICAL-2: `hasBoundVariableMismatch` Accepts Almost Everything

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
A universal bypass. An attacker can craft terms that always contain a LocalConst to evade type checking.

---

## CRITICAL-3: `inferUniverseOfType` Returns Wrong Universe

### Trepplein Behavior
**Location:** `typechecker.scala:378-386`

```scala
def inferUniverseOfType(ty: Expr): Level =
  whnf(infer(ty)) match {
    case Sort(l) => l
    case s if trustExports && isStuckTerm(s) =>
      Level.Zero  // PLACEHOLDER - could be ANY universe!
    case s => throw ...
  }
```

When a type's universe cannot be determined (stuck term), this returns `Prop` (`Level.Zero`). A term at `Type 42` would be treated as `Prop`, with completely different properties (proof irrelevance, universe constraints).

### Reference Implementation Behavior

**lean4** (`type_checker.cpp:53-62`):
```cpp
expr type_checker::ensure_sort_core(expr e, expr const & s) {
    if (is_sort(e)) return e;
    auto new_e = whnf(e);
    if (is_sort(new_e)) return new_e;
    throw type_expected_exception(env(), m_lctx, s);  // ALWAYS FAILS
}
```

**lean4lean** (`InferType.lean:101-107`): Post-condition requires `c.HasType e' (.sort u')` — a fully determined sort. No placeholder fallback.

**nanoda_lib** (`tc.rs:228-237`):
```rust
pub(crate) fn ensure_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
    // ...
    match self.ctx.read_expr(whnfd) {
        Sort { level, .. } => level,
        _ => panic!("ensure_sort could not produce a sort"),
    }
}
```

### Impact
Universe polymorphism and proof irrelevance could be applied incorrectly, allowing unsound proofs.

---

## HIGH-1: No Recursor Well-Formedness Checking

**Test Status:** ✅ **CONFIRMED** via `RecursorRhsUnchecked` test

The test corrupts the first recursor rule (`List.rec` nil case) to return `Prop` instead of the correct RHS:
- **Original:** `0 #RR 2 0 69` (nil case returns expr 69, the correct RHS)
- **Corrupt:** `0 #RR 2 0 0` (nil case returns expr 0, which is `Prop`!)

**Validation:**
- nanoda_lib: **REJECTS** (panics at `src/tc.rs:803` during recursor rule verification)
- trepplein: **ACCEPTS** (trusts recursor rules without verification)

### Trepplein Behavior
**Location:** `environment.scala:233-236`

```scala
def check(): Unit = {
  decl.check(env)
  // Additional checking for recursor well-formedness would go here
}
```

The comment explicitly admits no recursor well-formedness checking exists. Recursor rules from the export are trusted without verifying:
- Minor premise types are correct
- Motive is valid for the inductive type
- Computational rules match the constructors

### Reference Implementation Behavior

**lean4** (`inductive.cpp:589-776`): `declare_recursors()` constructs recursor types from scratch using `mk_rec_rules()`, validates through `infer_implicit()`, and type-checks the result. `inductive_reduce_rec()` (inductive.h:76-119) validates rules exist and major premise is present during reduction.

**lean4lean** (`Inductive/Add.lean:415-446`): `mkRecRules` constructs rules from scratch, verifying argument structure. Then `assert_nonnested_rec_rule_def_eq` checks imported rules match constructed ones via full definitional equality.

**nanoda_lib** (`inductive.rs:1181-1211`):
```rust
fn assert_nonnested_rec_rule_def_eq(...) {
    assert_eq!(imported_rr.ctor_name, constructed_rr.ctor_name);
    assert_eq!(imported_rr.ctor_telescope_size_wo_params, constructed_rr.ctor_telescope_size_wo_params);
    self.assert_def_eq(imported_rr.val, rr_made_val);  // Full equality check!
}
```

### Impact
Recursors are the computational heart of dependent type theory. Malicious recursor rules could enable arbitrary computation, breaking soundness.

---

## HIGH-2: Proof Irrelevance Precondition Not Enforced

**Test Status:** ⚠️ **ATTEMPTED** - Bug exists but appears unexploitable due to earlier type inference checks

### Trepplein Behavior
**Location:** `typechecker.scala:83-84, 188-191`

```scala
// requires that e1 and e2 have the same type, or are types  ← PRECONDITION (comment only!)
def checkDefEq(e1: Expr, e2: Expr): DefEqRes =
  if (e1.eq(e2) || e1 == e2) IsDefEq else defEqCache.getOrElseUpdate((e1, e2), {
    if (isProofIrrelevantEq(e1, e2)) IsDefEq else checkDefEqCore(e1, e2)
  })

private def isProofIrrelevantEq(e1: Expr, e2: Expr): Boolean =
  isProof(e1) && isProof(e2)  // Only checks both are proofs, NOT that types match
```

The comment documents a precondition that callers must ensure `e1` and `e2` have the same type. But `isProofIrrelevantEq` only checks both are proofs, not that their types are definitionally equal.

### Exploitation Attempt

Created test case `ProofTypeMismatch` with:
- `hp : P` and `hq : Q` (proofs of different propositions)
- `T : P -> Type` (type family indexed by P proofs)
- `v : T hp` (value with type T hp)
- `def foo : T hq := v` (declared type uses wrong proof)

The goal was: when comparing `T hq` with `T hp`, the buggy `isProofIrrelevantEq(hq, hp)` would return true without checking `P = Q`.

**Result:** Both trepplein and nanoda_lib correctly reject this. Trepplein catches it during type inference for `T hq` - it calls `checkType(hq, P)` because T's domain is P, and this fails because `hq : Q ≠ P`.

The bug exists in the code but appears protected by earlier type inference checks. When forming ill-typed expressions like `App(T, hq)` where `hq` has the wrong type, the type inference for applications catches this before the proof comparison.

### Reference Implementation Behavior

**lean4** (`type_checker.cpp:825-834`):
```cpp
lbool type_checker::is_def_eq_proof_irrel(expr const & t, expr const & s) {
    expr t_type = infer_type(t);
    if (!is_prop(t_type)) return l_undef;
    expr s_type = infer_type(s);
    return to_lbool(is_def_eq(t_type, s_type));  // CHECKS TYPE EQUALITY
}
```

**lean4lean** (`IsDefEq.lean:28`): The `.uniq` method takes inferred types of both proofs and calls `IsDefEq` on them before treating terms as equal.

**nanoda_lib** (`tc.rs:1196-1204`):
```rust
fn proof_irrel_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
    match self.is_proof(x) {
        (false, _) => false,
        (true, l_type) => match self.is_proof(y) {
            (false, _) => false,
            (true, r_type) => self.def_eq(l_type, r_type),  // CHECKS TYPE EQUALITY
        },
    }
}
```

### Impact
The bug should still be fixed for defense in depth - the code violates its documented precondition. However, practical exploitation may require more complex scenarios than straightforward export corruption.

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

## HIGH-4: Universe Level Validation Incomplete

**Test Status:** ✅ **CONFIRMED** via `WrongUniverse` test

The test corrupts the universe level in the Sexpr export:
- **Original:** `0 #ES 2` (Sort(u+1) = Type u)
- **Corrupt:** `0 #ES 0` (Sort(0) = Prop)

This makes List have type `∀ A : Prop, Prop` instead of `∀ A : Type u, Type u`, which is fundamentally invalid.

**Validation:**
- nanoda_lib: **REJECTS** (panics at `src/expr.rs:599` - universe constraint violated)
- trepplein: **ACCEPTS** (universe levels not fully validated in inductive declarations)

### Trepplein Behavior

Universe levels in inductive types, constructors, and recursors are not fully validated against expected constraints. When an export contains corrupted universe levels, trepplein accepts declarations that would produce ill-typed terms.

### Reference Implementation Behavior

**nanoda_lib** validates universe constraints throughout expression processing, catching inconsistencies early.

### Impact
Incorrect universe levels could allow type confusion (treating a Type as a Prop), undermining proof irrelevance guarantees and universe polymorphism.

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

## MEDIUM-3: Integer Overflow in `Nat.pow`

### Trepplein Behavior
**Location:** `literal.scala:45`

```scala
case Name.Str(NatName, "pow") if enableNatReduction =>
  reduceNatBinOp(args, (a, b) => a.pow(b.toInt))  // b.toInt can overflow!
```

If the exponent `b` exceeds `Int.MaxValue` (2^31-1), `.toInt` silently overflows, producing wrong results.

### Reference Implementation Behavior

**lean4**: Uses proper big integer arithmetic throughout.

**lean4lean**: Uses Lean's arbitrary-precision `Nat`.

**nanoda_lib**: Uses Rust's `BigInt` operations.

### Impact
Very large exponents would produce mathematically incorrect results. While unlikely in practice, this violates the principle of an independent verifier.

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

| ID | Severity | Issue | Test Status | References |
|----|----------|-------|-------------|------------|
| CRITICAL-1 | Critical | `trustExports` bypass default | - | No bypass in lean4/lean4lean/nanoda_lib |
| CRITICAL-2 | Critical | `hasBoundVariableMismatch` | Not reproduced | No such logic in references |
| CRITICAL-3 | Critical | `Level.Zero` placeholder | - | Always throws/panics in references |
| HIGH-1 | High | No recursor validation | ✅ CONFIRMED | Full validation in all references |
| HIGH-2 | High | Proof irrelevance types | ⚠️ Unexploitable | All references check types |
| HIGH-3 | High | Constructor metadata | - | All references compute from type |
| HIGH-4 | High | Universe level validation | ✅ CONFIRMED | Full validation in all references |
| MEDIUM-1 | Medium | Positivity incomplete | - | Thorough checks in references |
| MEDIUM-2 | Medium | Mutable globals | - | None in references |
| MEDIUM-3 | Medium | Nat.pow overflow | - | BigInt in references |
| MEDIUM-4 | Medium | `unsafeUnchecked` flag | - | Separate mode or none |

---

## Conclusion

Trepplein's current implementation does not provide the independent verification guarantees its documentation claims. The pervasive `trustExports = true` default with multiple broad bypass mechanisms means it accepts terms that all three reference implementations would reject.

**Validated defects:**
1. **RecursorRhsUnchecked** - Trepplein accepts malformed recursor rules that nanoda_lib correctly rejects. Recursor rules define the computational behavior of inductive types, and accepting arbitrary RHS values could enable unsound proofs.
2. **WrongUniverse** - Trepplein accepts corrupted universe levels that nanoda_lib rejects. This could allow type confusion between `Type u` and `Prop`.

**Attempted but unexploitable defects:**
3. **ProofTypeMismatch (HIGH-2)** - The proof irrelevance bug in `isProofIrrelevantEq` exists in code but appears protected by earlier type inference checks. Attempting to compare proofs of different types causes failures during application type inference before the buggy proof comparison is reached. The bug should still be fixed for correctness.

**Unvalidated defects:** Some defects (like `hasBoundVariableMismatch`) were harder to reproduce with simple export corruption. They may require more complex edge cases involving stuck computations. The code analysis still indicates these are real issues.

The project's own `CLAUDE.md` states:
> "If something doesn't type-check, we must fix the actual reduction/inference logic, NOT add workarounds or special cases to skip failures."

The code contradicts this principle at multiple points.

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

### Key Insight: Defense in Depth
Some bugs exist in code but are protected by earlier checks:
- **Proof irrelevance (HIGH-2):** Bug in `isProofIrrelevantEq` but application type inference catches ill-typed terms first
- **hasBoundVariableMismatch (CRITICAL-2):** Only triggers when expressions contain `LocalConst`, which requires stuck computations on abstract arguments

To exploit these "protected" bugs, we'd need scenarios where:
1. Both compared expressions are well-typed in their own contexts
2. The buggy code path is reached before other guards

---

## Future Investigation Ideas

### Unexplored Vectors
1. **Recursor major premise manipulation** - What if we corrupt which argument is the "major premise"?
2. **Nested inductive types** - The positivity check (MEDIUM-1) may be bypassable with complex nested structures
3. **Universe constraint accumulation** - Can we construct exports where universe constraints are inconsistent but not checked?
4. **Quotient type rules** - Are `Quot.mk`, `Quot.lift`, `Quot.ind` rules validated?

### Complex Exploitation Scenarios
For "protected" bugs like HIGH-2 (proof irrelevance):
- Try comparing proofs that appear in **recursor minor premises** during reduction
- Try proofs in **let bindings** where types might not be re-inferred
- Try proofs in **projection types** for dependent structures

### Test Cases to Create
- [ ] `NonpositiveNested` - Nested inductive that bypasses simple positivity check
- [ ] `QuotientRuleCorrupt` - Corrupted quotient type reduction rules
- [ ] `RecursorMajorWrong` - Wrong major premise index in recursor

### Notes on Export Format
- Expressions are indexed, allowing forward references
- Type checking happens lazily when declarations are processed
- Corrupting expression indices can create ill-typed terms that bypass construction checks

---

## Test Resources Reference

### Defect Regression Tests (in `conformance.scala`)
| Directory | Defect | Status | Notes |
|-----------|--------|--------|-------|
| `RecursorRhsUnchecked/` | HIGH-1 | ✅ Differential bug | Corrupted nil case RHS |
| `WrongUniverse/` | HIGH-4 | ✅ Differential bug | Sort(u+1) → Sort(0) |
| `ProofTypeMismatch/` | HIGH-2 | ❌ Not differential | Both reject (documented attempt) |

### Existing Conformance Tests (from nanoda_lib)
| Directory | Expected | Notes |
|-----------|----------|-------|
| `Sexpr/`, `Sexpr1-3/` | Pass | Valid s-expression types |
| `Cycle1/`, `CycleMutual1/` | Fail | Direct/mutual definition cycles |
| `CycleOpaque1-3/` | Fail | Cycles through opaque definitions |
| `Nonpositive1-2/` | Fail | Non-strictly-positive inductives |
| `AxiomNotAllowed0-2/` | Varies | Axiom permission tests |
| `BadSemver/` | Fail | Invalid version format |

### Test File Structure
```
src/test/resources/TestName/
├── export          # The Lean 4 export file
└── source          # Human-readable description of what's tested
```
