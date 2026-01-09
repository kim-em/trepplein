# Plan: Eliminate All Bypass Code

## Goal

**Remove `trustExports` entirely and pass Init with 0 bypasses.**

Currently, 439 type mismatches are silently bypassed during Init library checking. This is unacceptable for an independent type checker. Neither nanoda_lib nor the Lean 4 kernel have bypass mechanisms - they implement the type theory correctly.

---

## Root Cause Analysis (Updated)

Investigation reveals the primary issue is **typeclass instance methods not reducing to their implementations**.

### Example: `Nat.sub_le`

Expected type:
```
Nat.le (HSub.hSub n (Nat.succ x)) (Nat.sub n x)
```

Inferred type:
```
Nat.le (Nat.pred (Nat.sub n x)) (Nat.sub n x)
```

The problem: `HSub.hSub n ...` should reduce to `Nat.sub n ...` via the `instHSubNat` instance, but it's not reducing!

### Why This Matters

This explains most of the 439 bypasses:
- **291 "PProd.0 (Nat.rec ...)"**: These are stuck because the arguments to `Nat.rec` contain unreduced `HSub.hSub` instead of `Nat.sub`
- **38 Monad instances**: `Bind.0`, `Seq.0`, etc. are typeclass method projections not reducing
- **14 Iterator types**: Same pattern with `Iterator` typeclass methods

### The Fix

We need to properly reduce **structure projections on instance applications**:

```
HSub.hSub @Nat @Nat @Nat instHSubNat n x
  ↓ (reduce structure projection)
instHSubNat.hSub n x
  ↓ (reduce definition)
Nat.sub n x
```

---

## Revised Implementation Phases

### Phase 1: Fix Structure Projection Reduction (CRITICAL)

Structure field projections like `HSub.hSub` should reduce when applied to a constructor (instance).

**Current behavior**: `HSub.hSub ... instHSubNat ...` stays unreduced
**Expected behavior**: Reduces to `Nat.sub`

**Investigation needed**:
1. Trace `HSub.hSub` reduction in whnf
2. Check if `instHSubNat` is being recognized as a constructor
3. Verify projection reduction logic handles typeclass instances

### Phase 2: Verify Stuck Projection Comparison

After Phase 1, many "stuck projections" should no longer be stuck. Remaining cases may need structural comparison:

```scala
case (Proj(t1, i1, s1), Proj(t2, i2, s2)) if t1 == t2 && i1 == i2 =>
  checkDefEq(s1, s2)  // Already implemented at line 319
```

### Phase 3: Eta-Struct Implementation

For `PSigma.mk (PSigma.fst x) (PSigma.snd x) = x`:
- 3+ bypasses directly involve this pattern
- May help with other cases after Phase 1

### Phase 4: Verify and Disable `trustExports`

After implementing proper reductions:
1. Run Init with instrumentation to count remaining bypasses
2. Investigate any remaining cases
3. Set `trustExports = false`
4. Remove bypass code entirely

---

## Current Bypass Statistics

| Category | Count | Root Cause |
|----------|-------|------------|
| `PProd.0 (Nat.rec ...)` | 225 | Instance methods not reducing |
| `PProd.0 (List.rec ...)` | 66 | Instance methods not reducing |
| Monad instances | 38 | Direct instance projection issue |
| Iterator types | 14 | Instance projection issue |
| Eta-struct | 3 | Missing `S.mk x.1 ... x.n = x` |
| Other | ~93 | Various patterns |
| **Total** | **439** | |

---

## Technical Deep Dive: Instance Reduction

### How it should work (Lean 4)

1. `HSub` is a structure with field `hSub`
2. `instHSubNat` is a constructor: `HSub.mk Nat.sub`
3. `HSub.hSub` is the projection function
4. `HSub.hSub ... instHSubNat ...` should reduce by projection

### Current trepplein behavior

Looking at `reduceProjectionDirect`:
```scala
struct match {
  case Apps(Const(ctorName, _), args) =>
    // Check if this is a constructor for our type
```

The issue may be:
1. Instance definitions aren't being recognized as constructors
2. Or the projection isn't being applied correctly

### Investigation steps

1. Add debug output in `reduceProjectionDirect` for `HSub.hSub`
2. Check what `instHSubNat` looks like after whnf
3. Verify the constructor check is working

---

## Success Criteria

- [ ] `HSub.hSub ... instHSubNat ...` reduces to `Nat.sub`
- [ ] Similar for `Bind.bind`, `Pure.pure`, `Functor.map`, etc.
- [ ] Init library passes with `trustExports = false`
- [ ] 0 bypass conditions triggered
- [ ] `trustExports` parameter removed from codebase

---

## Non-Goals

- **NOT** making the bypass more permissive
- **NOT** adding new bypass conditions
- **NOT** "fixing" failures by trusting more things

---

## Reference Implementation Behavior

**Lean 4 kernel**: Structure projections reduce via `proj_reduce` in `type_checker.cpp`. Instances are structure values, so projecting a field from an instance extracts the implementation.

**nanoda_lib**: Similar handling - instance projections reduce to underlying definitions.

We must match this behavior exactly.
