# Trepplein Type Checker Defects

This document catalogs known defects in trepplein's type checking, validated by comparison against three reference implementations:
- **lean4** (C++) — The official Lean 4 kernel at `/tmp/lean4/src/kernel/`
- **lean4lean** (Lean 4) — Independent checker at `/tmp/lean4lean/`
- **nanoda_lib** (Rust) — Independent checker at `/tmp/nanoda_lib/`

---

## Current Status

**Goal:** Remove `trustExports` entirely and pass Init with 0 bypasses.

| Metric | Value |
|--------|-------|
| With `trustExports = true` | 439 silent bypasses, Init "passes" |
| With `trustExports = false` | 4420 type errors (down from 6091) |
| Target | 0 errors, 0 bypasses |

Recent fixes:
- Added literal reduction for nested expressions (HSub, HMod, HDiv)
- Added stuck projection comparison with whnf-based struct arg matching

---

## Root Cause Analysis

### Primary Issue: Instance Method Reduction

The core problem is **typeclass instance methods not reducing to their implementations**.

Example from `Nat.sub_le`:
```
Expected type:  Nat.le (HSub.hSub n (Nat.succ x)) (Nat.sub n x)
Inferred type:  Nat.le (Nat.pred (Nat.sub n x)) (Nat.sub n x)
```

The problem: `HSub.hSub n ...` should reduce to `Nat.sub n ...` via `instHSubNat`, but doesn't.

### How Instance Reduction Should Work

```
HSub.hSub @Nat @Nat @Nat instHSubNat n x
  ↓ (reduce structure projection)
instHSubNat.hSub n x
  ↓ (reduce definition)
Nat.sub n x
```

1. `HSub` is a structure with field `hSub`
2. `instHSubNat` is a constructor: `HSub.mk Nat.sub`
3. `HSub.hSub` is the projection function
4. `HSub.hSub ... instHSubNat ...` should reduce by projection

### Bypass Categories (from instrumentation with `trustExports = true`)

| Category | Count | Root Cause |
|----------|-------|------------|
| `PProd.0 (Nat.rec ...)` | 225 | Stuck projections - need structural comparison |
| `PProd.0 (List.rec ...)` | 66 | Same as above |
| Monad instances (Bind, Seq, etc.) | 38 | Instance methods not reducing |
| Iterator types | 14 | Instance projection issue |
| Eta-struct cases | 3 | Missing `S.mk x.1 x.2 = x` |
| Other | ~93 | Various patterns |
| **Total** | **439** | |

---

## CRITICAL-1: Missing Stuck Projection Comparison

**Status:** PARTIALLY IMPLEMENTED
**Impact:** 291 bypasses → reduced but not eliminated

### Current Implementation

When comparing `Proj(T, i, s1)` vs `Proj(T, i, s2)` where both are stuck:
1. If s1 == s2 syntactically: compare projection args
2. If s1 and s2 are Apps with the same head const and universe levels:
   - Compare their arguments after whnf normalization
   - If all args match: compare projection args

### Remaining Issue

Struct arguments that are definitionally equal but not syntactically equal after whnf still fail. For example, `PProd.mk A B` vs `PProd.mk A' B'` where A=A' and B=B' after deep reduction, but A≠A' after just whnf.

Using `checkDefEq` on struct bases directly causes stack overflow due to deep recursion.

### What Reference Implementations Do

**Lean 4 Kernel**: When comparing stuck projections:
1. First checks if both are projections on the same struct with same index
2. If so, compare the struct arguments
3. Has "cheap projection" mode that avoids over-reduction

**nanoda_lib**: Stuck projections must match structurally.

### Fix Required

```scala
case (Proj(t1, i1, s1), Proj(t2, i2, s2)) if t1 == t2 && i1 == i2 =>
  checkDefEq(s1, s2)  // Compare bases
```

---

## CRITICAL-2: Missing/Incomplete Eta-Struct Implementation

**Status:** PARTIAL (WIP commit has skeleton)
**Impact:** 3+ direct bypasses, may help others

### What's Missing

Lean 4's `try_eta_struct_core` (`type_checker.cpp:784`) handles:
```
PSigma.mk (PSigma.fst x) (PSigma.snd x) =def= x
```

The WIP commit has a partial implementation, but it's not triggering correctly for all cases.

### Fix Required

For single-constructor types (tracked in `inductiveInfo`):
- Recognize `Ctor(Proj_0(x), Proj_1(x), ..., Proj_n(x))` pattern
- Compare structurally with `x`
- Handle both anonymous projections (`Proj(T, i, x)`) and named projections (`T.fst x`)

---

## CRITICAL-3: Instance Projection Reduction

**Status:** NOT WORKING CORRECTLY
**Impact:** ~50+ bypasses for Monad/Applicative, possibly many more

### What's Happening

Projections on typeclass instances don't reduce:
- `Bind.bind` on a `Monad` instance stays unreduced
- `Pure.pure`, `Functor.map`, `Seq.seq` same issue

### Investigation Needed

1. Trace `reduceProjectionDirect` for `HSub.hSub`
2. Check if `instHSubNat` is recognized as a constructor after whnf
3. Verify projection reduction logic handles typeclass instances

### Reference

**Lean 4 kernel**: `proj_reduce` in `type_checker.cpp`. Instances are structure values, so projecting a field extracts the implementation.

---

## MEDIUM-1: Mutable Global State for Literal Reduction

**Status:** OPEN
**Location:** `literal.scala:12-13`

```scala
var enableNatReduction: Boolean = true
var enableStringReduction: Boolean = true
```

Reference implementations have no mutable state affecting reduction. Should be passed via constructor.

---

## MEDIUM-2: `unsafeUnchecked` Flag Exists

**Status:** OPEN
**Location:** `typechecker.scala:15`

Currently only used for pretty-printing (`main.scala:17`), but API allows misuse.

**Options:**
- Remove the flag entirely
- Rename to make misuse obvious (e.g., `DANGEROUS_skipAllTypeChecks`)

---

## Summary Table

| ID | Severity | Issue | Status |
|----|----------|-------|--------|
| CRITICAL-1 | Critical | Missing stuck projection comparison | Partial (whnf-based) |
| CRITICAL-2 | Critical | Incomplete eta-struct | Partial (WIP) |
| CRITICAL-3 | Critical | Instance projection reduction | Not working |
| MEDIUM-1 | Medium | Mutable globals | Open |
| MEDIUM-2 | Medium | `unsafeUnchecked` flag | Open |

---

## Resolved Defects

| ID | Issue | Resolution |
|----|-------|------------|
| HIGH-1 | No recursor well-formedness checking | Added validation in `RecursorMod.check()` |
| HIGH-2 | Proof irrelevance types not checked | `isProofIrrelevantEq` now verifies types are def-eq |
| HIGH-3 | Constructor metadata trusted | Validates numParams/numFields in `CtorMod.check()` |
| HIGH-4 | Universe level validation incomplete | Added in `IndMod.check()` |
| HIGH-5 | `lcProof` placeholder proofs | Removed entirely |
| MEDIUM-3 | Integer overflow in `Nat.pow` | Uses `intValueExact` |
| NESTED-1 | Nested recursor rule construction | Track numParams for all inductives |

---

## Implementation Priority

### Phase 1: Fix Stuck Projection Comparison (CRITICAL-1)

Should resolve ~291 bypasses. When both sides are stuck projections with same type/index, compare bases structurally.

### Phase 2: Fix Instance Projection Reduction (CRITICAL-3)

Root cause of many failures. Investigate why projections on instances don't reduce, fix `reduceProjectionDirect`.

### Phase 3: Complete Eta-Struct (CRITICAL-2)

Finish the WIP implementation. Should resolve 3+ bypasses and may help with other cases.

### Phase 4: Test and Iterate

1. After each fix, test with `trustExports = false`
2. Count remaining failures: `grep -c "wrong type" /tmp/trepplein-run.log`
3. Categorize new failure patterns
4. Repeat until 0 failures

### Phase 5: Remove Bypass Code

Once Init passes with `trustExports = false`:
1. Remove `trustExports` parameter entirely
2. Remove all bypass code paths in typechecker.scala
3. Clean up debugging variables

---

## Success Criteria

- [ ] Stuck projections compare structurally
- [ ] Instance projections reduce correctly
- [ ] Eta-struct handles all single-constructor types
- [ ] Init library passes with `trustExports = false`
- [ ] 0 bypass conditions triggered
- [ ] `trustExports` parameter removed from codebase

---

## Non-Goals

- **NOT** making the bypass more permissive
- **NOT** adding new bypass conditions
- **NOT** "fixing" failures by trusting more things

The purpose of an independent type checker is to independently verify.

---

## Verification Commands

```bash
# Build
sbt stage

# Test
JAVA_HOME=/opt/homebrew/opt/openjdk ./target/universal/stage/bin/trepplein \
  -J-Xss16m /tmp/init.lean4export 2>&1 | tee /tmp/test.log | tail -20

# Count errors
grep -c "wrong type" /tmp/test.log

# Find specific patterns
grep "wrong type:" /tmp/test.log | head -20
```
