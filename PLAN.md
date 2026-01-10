# Plan: Fix Remaining Type Errors

## Current Status (Updated 2026-01-10)

After implementing native `Nat.gcd` and `Int.natAbs` support, we have **6 remaining errors**.

---

## Progress Summary

| Fix | Errors Before | Errors After |
|-----|---------------|--------------|
| CRITICAL-1: Stuck projection comparison | 6091 | 4420 |
| CRITICAL-2: Eta-struct | 4420 | ~4400 |
| CRITICAL-3: Instance projection | ~4400 | ~100 |
| CRITICAL-4: Bool.true shortcut | ~100 | 24 |
| Native Nat.gcd + Int.natAbs | 24 | **6** |

---

## Remaining 6 Errors - Deep Analysis

### 1-3. UInt16/32/64.succMany?_ofBitVec

**Issue**: `PProd.0 (Nat.rec ... n)` stuck on large numbers (65535, 4B, 18B)

**Lean 4 approach** (from `type_checker.cpp`):
- Uses `eagerReduce` mode (`m_eager_reduce = true`) for these computations
- In eager mode, `reduce_nat` is called even with free variables (line 969-975)
- The kernel actually executes the full `Nat.rec` reduction
- For large numbers, this is expensive but works

**Brainstorm solutions**:
1. **Trust eagerReduce** - When we see `eagerReduce _ arg`, bypass type checking for `arg`
   - Pro: Simple, matches how proofs are constructed
   - Con: Defeats independent verification goal

2. **Native PProd.0/PProd.1 on Nat.below** - Recognize specific pattern
   - `PProd.0 (Nat.below motive (Nat.succ n)) = motive n`
   - Pro: Correct, fast
   - Con: Complex to implement, pattern-specific

3. **Implement VM-based evaluation** - Add bytecode interpreter
   - Pro: General solution for all expensive computations
   - Con: Significant implementation effort

### 4. System.Platform.numBits_eq

**Issue**: `Subtype.0 (System.Platform.getNumBits Unit.unit)` doesn't reduce

**Lean 4 approach**:
- `System.Platform.getNumBits` is defined as:
  ```lean
  @[extern "lean_system_platform_nbits"]
  opaque getNumBits : Unit → { n : Nat // n = 32 ∨ n = 64 }
  ```
- It's an `opaque extern` - the kernel doesn't reduce it
- In the kernel, `numBits_eq` proofs work because platform-specific native code is linked

**Brainstorm solutions**:
1. **Hardcode platform** - Assume 64-bit, make `getNumBits Unit.unit = 64`
   - Pro: Simple
   - Con: Incorrect for 32-bit platforms

2. **Add platform configuration** - Command-line flag `--platform-bits=64`
   - Pro: Flexible, documentable
   - Con: Export files become platform-dependent

3. **Skip platform proofs** - Accept `System.Platform.*` as trusted
   - Pro: Acknowledges reality
   - Con: Small hole in verification

### 5. String.toByteArray_empty

**Issue**: Type mismatch `Type 0 !=def List α`

**Debug trace showed**: `List.nil : Type 0` vs expected `List α`

This appears to be a universe level mismatch or reduction issue. Needs more investigation.

**Brainstorm solutions**:
1. **Investigate List.nil reduction** - Check if type parameters are being handled correctly
2. **Check universe handling** - May be a bug in universe level comparison

### 6. WellFounded.fixF_eq

**Issue**: `Acc.rec` doesn't reduce properly on `Acc.intro`

**Lean 4 approach** (from `inductive.h`):
- `Acc.rec` has `isK = false` in the export (confirmed: `#REC ... isK 0`)
- K-reduction via `to_cnstr_when_K` returns unchanged for non-nullary constructors
- The recursor should fire normally on `Acc.intro x h` constructor

**Debug trace showed**:
- Expected: motive applied to `Acc.intro x h`
- Inferred: reflexivity proof about `WellFounded.fixF`
- The `Acc.rec` rule should fire but types don't match

**Brainstorm solutions**:
1. **Check Acc.rec rule application** - Verify recursor rules are being applied correctly
2. **Trace Acc.rec reduction** - Add debug to see if the rule matches and what goes wrong
3. **Check type inference for Acc proofs** - May be inferring wrong types

---

## Lean 4 Kernel Key Insights

From `/tmp/lean4/src/kernel/type_checker.cpp`:

1. **eagerReduce mode** (lines 159-176):
   - Triggered by `eagerReduce _ arg` pattern in proof terms
   - Sets `m_eager_reduce = true` during type checking
   - Enables more aggressive reduction (line 969)

2. **Native Nat operations** (lines 613-626):
   - `Nat.add`, `sub`, `mul`, `div`, `mod`, `gcd`, `beq`, `ble`, etc.
   - All use `reduce_bin_nat_op` or `reduce_bin_nat_pred`

3. **K-reduction** (from `inductive.h` lines 28-50):
   - `to_cnstr_when_K` converts any proof to canonical constructor
   - Only works for nullary constructors (returns unchanged otherwise)
   - Used for `Eq.rec`, `HEq.rec`, etc. where `isK = true`

4. **Projection reduction** (lines 358-386):
   - `reduce_proj_core` extracts constructor field
   - Uses `whnf` on struct to get constructor form

---

## Next Steps (Priority Order)

1. **WellFounded.fixF_eq** - Debug Acc.rec rule application
   - Most likely to be a bug in existing logic

2. **String.toByteArray_empty** - Investigate type mismatch
   - May reveal a bug in List handling

3. **Platform.numBits_eq** - Add platform configuration
   - Clean solution with `--platform-bits` flag

4. **UInt succMany** - Consider eagerReduce trust mode
   - Last resort, requires careful documentation

---

## Verification

```bash
sbt stage
JAVA_HOME=/opt/homebrew/opt/openjdk ./target/universal/stage/bin/trepplein \
  -J-Xss16m /tmp/init.lean4export 2>&1 | tee /tmp/test.log | tail -30
grep -c "wrong type" /tmp/test.log
```

**Current:** 6 errors
**Target:** 0 errors (or minimal with documented exceptions)
