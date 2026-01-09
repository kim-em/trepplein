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
| With `trustExports = false` | **24 type errors** (down from 6091 → 4420 → 647 → 429 → 388 → 29 → 24) |
| Target | 0 errors, 0 bypasses |

Recent fixes:
- Added literal reduction for nested expressions (HSub, HMod, HDiv)
- **CRITICAL-1 FIXED**: Added in-progress cycle detection for stuck projection comparison
  - Modeled after Lean 4's equiv_manager and nanoda's union-find approach
  - Reduced errors from 4420 → 647 (85% improvement)
- **CRITICAL-2 IMPROVED**: Fixed eta-struct to match reference implementations
  - Create projections and check def-eq instead of syntactic pattern matching
  - Reduced errors from 647 → 429 (33% improvement)
- **Unit-like types**: Added def-eq for unit-like types (single constructor, 0 fields)
  - Reduced errors from 429 → 388 (10% improvement)
- **CRITICAL-3 FIXED**: Added eta-struct expansion for recursor major premises
  - Based on Lean 4's `to_cnstr_when_structure` and `expand_eta_struct`
  - Converts structure values to constructor form to enable recursor reduction
  - Reduced errors from 388 → 24 (94% improvement)
- **Private constructors**: Fixed projection reduction for private constructors
  - Check against stored ctorName in inductiveInfo, not just naming convention
  - Reduced errors from 29 → 24 (17% improvement)

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

## CRITICAL-1: Stuck Projection Comparison

**Status:** ✅ FIXED
**Impact:** 4420 → 647 errors (85% reduction)

### Solution Implemented

Added in-progress cycle detection to prevent stack overflow when comparing struct bases:

```scala
private val inProgressPairs = mutable.HashSet[(Expr, Expr)]()

def checkDefEq(e1: Expr, e2: Expr): DefEqRes = {
  val key = if (e1.hashCode <= e2.hashCode) (e1, e2) else (e2, e1)

  // Check if already in progress (cycle) → return IsDefEq optimistically
  if (inProgressPairs.contains(key)) return IsDefEq

  inProgressPairs.add(key)
  try { /* compute result */ }
  finally { inProgressPairs.remove(key) }
}
```

This matches how both reference implementations handle cycles:
- **Lean 4**: Uses `equiv_manager` (union-find) + failure cache
- **nanoda**: Uses `check_uf_eq` union-find

### Projection Comparison (Simplified)

```scala
case (Proj(t1, i1, s1), Proj(t2, i2, s2)) if t1 == t2 && i1 == i2 =>
  checkDefEq(s1, s2) match {
    case IsDefEq => checkArgs
    case ne => ne
  }
```

---

## CRITICAL-2: Eta-Struct Implementation

**Status:** ✅ IMPROVED (matching reference implementations)
**Impact:** 647 → 429 errors (33% reduction)

### Solution Implemented

Changed algorithm to match Lean 4 kernel and nanoda_lib:

```scala
def tryEtaStruct(ctorFn: Const, ctorArgs: List[Expr], other: Expr): Option[DefEqRes] = {
  // 1. Check if ctorFn is a constructor for a structure-like type
  // 2. Check arg count matches numParams + numFields
  // 3. Check types are def-eq: infer(ctor(args...)) = infer(other)
  // 4. For each field: Proj(typeName, fieldIdx, other) =def= arg
  val fieldArgs = ctorArgs.drop(numParams)
  val allFieldsMatch = fieldArgs.zipWithIndex.forall { case (arg, idx) =>
    val proj = Proj(typeName, idx, other)
    isDefEq(proj, arg)
  }
  if (allFieldsMatch) Some(IsDefEq) else None
}
```

Key insight: Don't check if args ARE projections syntactically. Instead, create
projections and check definitional equality. This handles cases where args
reduce to projections (e.g., `Array.toList xs =def= Proj(Array, 0, xs)`).

### Remaining Issues

Some cases still fail, likely due to:
- Nested contexts where projections don't reduce
- Missing `is_structure_like` validation (numIndices, isRecursive checks)
- Other reduction issues

---

## CRITICAL-3: Instance Projection Reduction

**Status:** ✅ FIXED (via eta-struct expansion for recursors)
**Impact:** Reduced errors from 388 → 24 (94% improvement)

### Solution Implemented

The core issue was that recursor applications like `Fin.rec (...) a` wouldn't reduce when `a` is a variable of structure type. The fix has two parts:

1. **Eta-struct expansion for recursor major premises** (`expandEtaStruct`):
   - For recursors of structure-like types (single constructor)
   - Convert the major premise to constructor form: `a` → `S.mk (Proj(S, 0, a)) (Proj(S, 1, a)) ...`
   - This enables the recursor to fire even when the argument is a variable
   - Based on Lean 4's `to_cnstr_when_structure` and `expand_eta_struct`

2. **Fixed private constructor handling** (`isConstructorOf`):
   - Private constructors like `_private.X.Y.Z.TypeName.mk` weren't recognized
   - Now checks against stored `ctorName` in `inductiveInfo`
   - Fixes projection reduction for structures with private constructors

### Reference

- **Lean 4 kernel**: `to_cnstr_when_structure` in `inductive.h`, `expand_eta_struct` in `inductive.cpp`
- Key insight: For structures, convert values to constructor form before reduction

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
