# Trepplein Type Checker Defects

This document catalogs known defects in trepplein's type checking, validated by comparison against:
- **lean4** (C++) — The official Lean 4 kernel at `/tmp/lean4/src/kernel/`
- **nanoda_lib** (Rust) — Independent checker at `/tmp/nanoda_lib/`

---

## Core Principle: No Cheating

Trepplein is an **independent type checker**. Its value comes from independently verifying Lean 4 proofs. Any "fix" that bypasses actual verification defeats this purpose.

**We will NOT:**
- Add bypass conditions to skip failing checks
- Trust computations without performing them
- Accept type mismatches as "probably fine"
- Use `trustExports` or similar escape hatches

**We WILL:**
- Implement correct reduction rules
- Add missing native operations (like `Nat.gcd`)
- Fix bugs in our type checking logic
- Document any fundamental limitations honestly

---

## Current Status

| Metric | Value |
|--------|-------|
| Init library type errors | **5** |
| Bypasses | **0** (trustExports disabled) |
| Target | **0 errors, 0 bypasses** |

Progress: 6091 → 4420 → 647 → 429 → 388 → 29 → 24 → 6 → **5**

---

## Resolved Defects (Critical)

### CRITICAL-1: Stuck Projection Comparison ✅

**Problem:** When comparing `Proj(T, i, s1)` vs `Proj(T, i, s2)` where both struct bases were "stuck" (couldn't reduce to constructors), we'd fail to compare them correctly. This caused stack overflow or false negatives.

**Solution:** Added in-progress cycle detection (`inProgressPairs` set) to prevent infinite loops, then simply call `checkDefEq(s1, s2)` on the bases. This matches Lean 4's `equiv_manager` and nanoda's union-find approach.

**Impact:** 4420 → 647 errors (85% reduction)

### CRITICAL-2: Eta-Struct Implementation ✅

**Problem:** Failed to recognize `S.mk x.1 x.2 ... x.n = x` for single-constructor structures.

**Solution:** Create actual projections and check definitional equality rather than pattern-matching syntactically. For `S.mk args...` vs `other`, check that each `arg[i] =def= Proj(S, i, other)`.

**Impact:** 647 → 429 errors (33% reduction)

### CRITICAL-3: Instance Projection Reduction ✅

**Problem:** Recursor applications like `Fin.rec motive minor a` wouldn't reduce when `a` is a variable of structure type, because the major premise wasn't in constructor form.

**Solution:** Implemented `expandEtaStruct` to convert structure values to constructor form before recursor reduction: `a` → `S.mk (Proj(S, 0, a)) (Proj(S, 1, a)) ...`. Based on Lean 4's `to_cnstr_when_structure` and `expand_eta_struct`.

**Impact:** 388 → 24 errors (94% reduction)

### CRITICAL-4: Omega/Grind Computation ✅

**Problem:** `Coeffs.gcd` computations in Omega/Grind proofs didn't complete because `Nat.gcd` and `Int.natAbs` weren't reducing natively.

**Solution:** Added native reduction for `Nat.gcd` (using `BigInt.gcd`) and `Int.natAbs` (using `value.abs`), matching Lean 4's `reduce_bin_nat_op`.

**Impact:** 24 → 6 errors (75% reduction)

### CRITICAL-5: Indexed Recursor Rule Construction ✅

**Problem:** Recursor rules for indexed inductive types (like `Acc.rec`) had mismatched de Bruijn indices between the LHS pattern and RHS body. The exported rule RHS doesn't include index parameters as lambdas - they're implicit in the constructor pattern.

**Solution:** Separate `numFixed` (for LHS with indices) from `numFixedForRHS` (without indices). Use constructor field Vars for index positions in LHS, matching how the RHS references them.

**Impact:** 6 → 5 errors (fixed `WellFounded.fixF_eq`)

---

## Resolved Defects (High/Medium)

| ID | Issue | Resolution |
|----|-------|------------|
| HIGH-1 | No recursor well-formedness checking | Added validation in `RecursorMod.check()` |
| HIGH-2 | Proof irrelevance types not checked | `isProofIrrelevantEq` now verifies types are def-eq |
| HIGH-3 | Constructor metadata trusted | Validates numParams/numFields in `CtorMod.check()` |
| HIGH-4 | Universe level validation incomplete | Added in `IndMod.check()` |
| NESTED-1 | Nested recursor rule construction | Track numParams for all inductives |

---

## Open Defects

### OPEN-1: Nat.below Type Computation

**Status:** OPEN (3 errors: UInt16/32/64.succMany?_ofBitVec)

**Problem:** `PProd.0 (Nat.rec ... n)` stuck when `n` is large (65535, 4B, 18B). Computing `Nat.below` requires structural recursion on `n`, which is O(n).

**Root cause:** `Nat.below motive n` is computed via `Nat.rec`, producing a nested `PProd` structure. Extracting with `PProd.0` requires the full computation.

**Lean 4 approach:** Uses `eagerReduce` mode which actually executes the full reduction. For large numbers, this is slow but works.

**Potential fixes (in order of preference):**
1. Native `PProd` projection on `Nat.below` pattern (recognize and compute directly)
2. Implement interpreter/VM for expensive computations
3. Document as known limitation for very large numbers

### OPEN-2: Platform-Specific Opaque

**Status:** OPEN (1 error: System.Platform.numBits_eq)

**Problem:** `System.Platform.getNumBits` is an `@[extern]` opaque that returns 32 or 64 depending on the platform. Without platform info, we can't reduce it.

**Lean 4 approach:** Links native code that returns the actual platform value.

**Potential fixes:**
1. Add `--platform-bits=64` configuration flag
2. Document as platform-dependent (user must verify on target platform)

### OPEN-3: String.toByteArray_empty Type Mismatch

**Status:** OPEN (1 error)

**Problem:** Type mismatch `Type 0 !=def List α`. Appears to be a universe level or type parameter issue.

**Needs:** Further investigation into List handling and universe levels.

---

## Code Quality Issues

### MEDIUM-1: Mutable Global State

**Location:** `literal.scala:12-13`
```scala
var enableNatReduction: Boolean = true
var enableStringReduction: Boolean = true
```

Should be passed via constructor, not global state.

### MEDIUM-2: `unsafeUnchecked` Flag

**Location:** `typechecker.scala:15`

Currently only used for pretty-printing, but API allows misuse. Consider removing or renaming to make misuse obvious.

---

## Verification

```bash
sbt stage
JAVA_HOME=/opt/homebrew/opt/openjdk ./target/universal/stage/bin/trepplein \
  -J-Xss16m /tmp/init.lean4export 2>&1 | tee /tmp/test.log | tail -30
grep -c "wrong type" /tmp/test.log
```

Current: **6 errors**
Target: **0 errors**
