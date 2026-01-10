# Plan: Fix Remaining Type Errors

## Current Status (Updated 2026-01-10)

After implementing native `Nat.gcd` and `Int.natAbs` support, we went from **24 errors to 6 errors**.

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

## Remaining 6 Errors

### 1. UInt16.succMany?_ofBitVec
### 2. UInt32.succMany?_ofBitVec
### 3. UInt64.succMany?_ofBitVec

**Issue**: `PProd.0 (Nat.rec ...)` stuck on `Nat.below` computation

These involve `Nat.below` type computation which requires `Nat.rec` on large numbers (65535, 4294967295, 18446744073709551615). The `Nat.rec` can't complete because it would require billions of iterations.

**Root cause**: `Nat.below motive (Nat.succ n)` = `PProd (motive n) (Nat.below motive n)` is computed via `Nat.rec`. For large `n`, this is impractical.

**Potential fix**: Add native support for `PProd.0` / `PProd.1` projection on `Nat.below` patterns.

### 4. System.Platform.numBits_eq

**Issue**: `Subtype.0 (System.Platform.getNumBits Unit.unit)` is stuck

`System.Platform.getNumBits` is an opaque constant that returns 32 or 64 depending on the platform. Without platform information, this can't reduce.

**Cannot be fixed** without hardcoding platform assumptions or adding platform configuration.

### 5. String.toByteArray_empty

**Issue**: Type mismatch `Type 0 !=def List α`

Needs investigation - appears to be a type-level mismatch.

### 6. WellFounded.fixF_eq

**Issue**: `Acc.rec` K-like reduction needed

This requires special handling for `Acc.rec` similar to K-reduction for equality proofs.

---

## Changes Implemented (This Session)

### Native Nat.gcd Support
```scala
private val NatGcdName = Name.mkStr(NatName_, "gcd")

// In binary Nat operations:
case NatGcdName => aVal.gcd(bVal)
```

### Native Int.natAbs Support
```scala
private val IntNatAbs = Name.mkStr(IntName, "natAbs")

// Int.natAbs : Int → Nat
if ((n eq IntNatAbs) && as0.size >= 1) {
  extractIntValue(whnf(as0(0))).foreach { value =>
    return Some(NatLit(value.abs))
  }
}
```

---

## Next Steps

1. **Native Nat.below support** (3 errors) - Recognize `PProd` projections on `Nat.below` patterns
2. **String.toByteArray_empty investigation** (1 error) - Understand type mismatch
3. **Acc.rec K-reduction** (1 error) - Add K-like reduction for accessibility proofs
4. **Platform.numBits_eq** (1 error) - Consider if this should be configurable

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
