# Remaining Issues: Where Trepplein is Less Strict Than Reference Implementations

## Summary

With instrumentation, we found that **439 type checking bypasses** occur during the Init library check. While Init "passes" (0 reported failures), this is because `trustExports` allows certain mismatches to be silently accepted. Neither nanoda_lib nor the Lean 4 kernel have such bypass mechanisms.

---

## Issue 1: Missing Eta-Struct (HIGH PRIORITY)

### What's Happening
Trepplein bypasses 3+ cases like:
```
PSigma.mk (PSigma.fst x) (PSigma.snd x) !=def x
```

### What Reference Implementations Do

**Lean 4 Kernel** (`type_checker.cpp:784`):
```cpp
bool type_checker::try_eta_struct_core(expr const & s1, expr const & s2) {
    // If s2 = S.mk x.1 x.2 ... x.n and s1 = x, they're definitionally equal
}
```

**nanoda_lib**: Has similar eta-struct handling.

### Missing in Trepplein
We have no `tryEtaStruct` implementation. The `PSigma`, `PProd`, `Prod`, `Sigma`, etc. eta-contractions are not handled.

### Impact
Without `trustExports`, these would fail. We're bypassing instead of correctly computing equality.

---

## Issue 2: Projections on Stuck Recursors (HIGH PRIORITY)

### What's Happening
**291 bypasses** for patterns like:
- `PProd.0 (Nat.rec ...)` (225 cases)
- `PProd.0 (List.rec ...)` (66 cases)

These are projections on recursor applications where the major premise is abstract (a variable).

### What Reference Implementations Do

**Lean 4 Kernel**: When comparing stuck projections:
1. First checks if both are projections on the same struct with same index
2. If so, compare the struct arguments
3. Has "cheap projection" mode that avoids over-reduction

**nanoda_lib**: Stuck projections must match structurally. If `PProd.0 (Nat.rec ... x)` appears on both sides with the same `x`, they're equal.

### Missing in Trepplein
We try to reduce projections and recursors, fail, then bypass. We should instead:
1. Recognize stuck projections
2. Compare them structurally (same base, same index → equal)

### Impact
We're accepting things as "bypass" that should be proven equal via structural comparison.

---

## Issue 3: Monad/Applicative Instance Mismatches (MEDIUM PRIORITY)

### What's Happening
**30+ bypasses** for patterns like:
- `Bind.0 Monad.1 inst._@...` (20 cases)
- `Seq.0 Applicative.2 Monad.0 inst._@...` (10 cases)
- `Functor.0 Applicative.0 Monad.0 inst._@...` (8 cases)
- `Pure.0 Applicative.1 Monad.0 inst._@...` (7 cases)

### Root Cause
These appear to be cases where a typeclass instance is accessed through different paths (e.g., `Monad.toBind` vs direct `Bind` instance) and should be definitionally equal but aren't reducing to the same form.

### What Reference Implementations Do
This requires deeper investigation, but likely involves proper handling of:
- Structure field projections
- Instance coercions
- Diamond inheritance patterns

---

## Issue 4: `trustExports` Flag Still Has Effect

### Current State
`trustExports = true` is passed to TypeChecker in `environment.scala` for all declaration checks:
- Line 64: `DefMod.check()`
- Line 133: `TheoremMod.check()`
- Line 151: `OpaqueMod.check()`
- Line 322: `RecursorMod.check()`

### Active Bypass Points
1. **`checkType`** (line 1923): Main bypass - allows type mismatches when stuck terms or local constants are involved
2. **`inferUniverseOfType`** (line 2036): Returns placeholder universe for stuck terms
3. **`infer` for applications** (line 2072): Returns application as stuck type
4. **`inferProjType`** (lines 2274, 2289): Returns projection as stuck type

### Reference Implementation Comparison
- **nanoda_lib**: No trust mode. Either matches or fails.
- **Lean 4 kernel**: No bypass. Uses multiple strategies, then fails if nothing works.

---

## Issue 5: `unsafeUnchecked` Flag Exists

### Current State
`TypeChecker(env, unsafeUnchecked = true)` skips argument checking entirely.

Currently only used for pretty-printing (`main.scala:17`), but the API allows misuse.

### Reference Implementations
- **nanoda_lib**: No such flag
- **Lean 4 kernel**: Has `infer_only` mode, but it's a separate code path that clearly doesn't claim to verify

---

## Issue 6: Mutable Global State

### Current State
`literal.scala:12-13`:
```scala
var enableNatReduction: Boolean = true
var enableStringReduction: Boolean = true
```

These can be toggled, affecting whether `Nat.add`, `Nat.mul`, etc. reduce.

### Reference Implementations
No mutable state affecting reduction behavior.

---

## Recommendations

### Priority 1: Implement Eta-Struct
Add `tryEtaStruct` in `checkDefEq`:
```scala
def tryEtaStruct(e1: Expr, e2: Expr): Boolean = {
  // If e2 = S.mk(x.1, x.2, ..., x.n) and e1 = x, they're equal
  // For single-constructor types only
}
```

### Priority 2: Fix Stuck Projection Comparison
When comparing stuck projections, check structural equality:
```scala
case (Proj(t1, i1, s1), Proj(t2, i2, s2)) if t1 == t2 && i1 == i2 =>
  checkDefEq(s1, s2)  // Compare bases
```

### Priority 3: Remove `trustExports`
Once eta-struct and stuck projection handling are correct, the bypasses should no longer be needed. Then:
1. Set `trustExports = false` for all checks
2. Remove the bypass code paths entirely
3. Verify Init still passes

### Priority 4: Remove `unsafeUnchecked`
Either:
- Remove the flag entirely
- Or rename to make misuse obvious (e.g., `DANGEROUS_skipAllTypeChecks`)

### Priority 5: Remove Mutable State
Make literal reduction configuration immutable, passed via constructor.

---

## Verification After Fixes

With correct implementations:
- All 50502 Init declarations should pass with `trustExports = false`
- No bypass code should be triggered
- Behavior should match nanoda_lib and Lean 4 kernel exactly

---

## Current Bypass Statistics (Init Library)

| Category | Count | Description |
|----------|-------|-------------|
| `PProd.0 (Nat.rec ...)` | 225 | Projections on Nat recursors |
| `PProd.0 (List.rec ...)` | 66 | Projections on List recursors |
| Monad instances | 38 | Bind/Seq/Functor/Pure mismatches |
| Iterator types | 14 | Std.Iterators patterns |
| Eta-struct | 3 | PSigma.mk cases |
| Other | ~93 | Various patterns |
| **Total** | **439** | Bypassed type checks |
