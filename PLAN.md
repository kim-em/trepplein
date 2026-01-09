# Plan: Fix Type Checking Failures

## Executive Summary

Both reference implementations (nanoda_lib and Lean 4 kernel) are **strictly correct** - neither has bypass mechanisms for stuck terms. Trepplein's `trustExports` is a deviation that should be eliminated, not re-enabled. The failures indicate missing features that need to be implemented.

## Current Status

With `canBypass = false`, **328 declarations** fail type checking in the Init export.

## Key Insight from Reference Implementations

### nanoda_lib (Rust)
- **NO bypass at all** - either reduces or stays stuck
- Stuck projections must match structurally
- `Quot.lift` only reduces if arg is literally `Quot.mk`
- Strictly fails if terms don't match

### Lean 4 Kernel (C++)
- **NO bypass either** - tries multiple strategies, then fails
- Has `try_eta_struct_core` for structure eta-expansion
- Has proof irrelevance for Props
- Has `eagerReduce` mode for forcing computation
- Returns false if nothing matches - no trust mode

**Conclusion**: We need to implement the missing features, not bypass failures.

---

## Failure Categories and Fixes

### Category 1: Projections on Recursors (~61 failures)
**Pattern**: `PProd.0 (List.rec ...)`, `PProd.0 (Nat.rec ...)`

**Root Cause**: When projecting from a recursor application, if the major premise is abstract, the recursor can't reduce, so the projection stays stuck.

**What Lean 4 does**:
- Uses "cheap projection" mode that doesn't unfold definitions
- Has eta-struct expansion: `e = S.mk e.1 e.2 ... e.n` for single-constructor types
- If both sides are stuck projections with equal bases, they're equal

**Fix Strategy**:
1. Implement `tryEtaStruct` expansion in `checkDefEq`
2. Add cheap vs full reduction modes for projections
3. When comparing stuck projections, check structural equality

**Files**: `typechecker.scala`

### Category 2: Quotient Operations (25 failures)
**Pattern**: `Quot.lift f h q` where `q` is not literally `Quot.mk a`

**Root Cause**: Quotient reduction only fires when the quotient argument is syntactically `Quot.mk a`.

**What Lean 4 does**:
- `quot_reduce_rec` (quot.h:39) reduces major premise via WHNF first
- Only then checks if it's a `Quot.mk`
- If not, reduction is stuck (not bypassed)

**Fix Strategy**:
1. In `reduceOneStep`, add special case for `Quot.lift`/`Quot.ind`
2. Reduce the major argument (quotient value) via `whnf` first
3. Then check if it became `Quot.mk a`

**Files**: `typechecker.scala`, `quotient.scala`

### Category 3: Decidability Not Computing (18 failures)
**Pattern**: `Bool.true ... Prod.0 (Option.rec ...)`

**Root Cause**: `ite` expressions have decidable instances that don't reduce to `Bool.true/false`.

**What Lean 4 does**:
- Has `eagerReduce` wrapper that forces full reduction
- When `m_eager_reduce` is set, closed terms are fully reduced
- Has native reduction for Nat/Bool operations
- Uses `reduce_native` for compiled Lean code

**Fix Strategy**:
1. Verify `eagerReduce` mode is properly propagating
2. Ensure decidable instances (like `Nat.decEq`, `Nat.decLt`) have proper reduction rules
3. Add more aggressive reduction for Bool-returning expressions in type checking

**Files**: `typechecker.scala`, possibly `literal.scala`

### Category 4: Proof Irrelevance Not Reached (~100+ failures)
**Pattern**: Various stuck terms that are actually proofs

**Root Cause**: Proof irrelevance check is applied, but fails to recognize proofs when type inference fails on stuck terms.

**What Lean 4 does**:
- `is_def_eq_proof_irrel` (line 827): If both terms have Prop type, compare only their types
- Applied as part of the equality algorithm, not as last resort

**Fix Strategy**:
1. Apply proof irrelevance earlier in `checkDefEq`, not just as fallback
2. Improve `isProof` to handle stuck terms (infer from context)
3. When comparing stuck terms, check if they're both proofs first

**Files**: `typechecker.scala`

### Category 5: Eta-Struct Missing
**Pattern**: Structure values not recognized as equal to constructor applications

**Root Cause**: Trepplein lacks `try_eta_struct` from the Lean 4 kernel.

**What Lean 4 does**:
- `try_eta_struct_core` (line 784): If one side is `S.mk x.1 x.2 ...`, it's equal to `x`
- `expand_eta_struct` (inductive.cpp:98): Converts `e : S` to `S.mk e.1 ... e.n`

**Fix Strategy**:
1. Implement `tryEtaStruct` in `checkDefEq`
2. For single-constructor types, expand both sides to constructor form
3. Compare field-by-field

**Files**: `typechecker.scala`

---

## Implementation Phases

### Phase 1: Eta-Struct Expansion (HIGH IMPACT)
**Estimate**: Moderate complexity

Add `tryEtaStruct` to handle structure eta-expansion:

```scala
// In checkDefEq, when comparing stuck terms:
def tryEtaStruct(e1: Expr, e2: Expr): Boolean = {
  // If e2 = S.mk(x.1, x.2, ..., x.n) and e1 = x, they're equal
  // Or expand e1 to S.mk(e1.1, ..., e1.n) and compare
}
```

This may resolve many projection-on-recursor failures where the proof structure matches.

### Phase 2: Quotient Reduction Fix (25 failures)
**Estimate**: Straightforward

Modify `reduceOneStep` to handle `Quot.lift`:

```scala
case Apps(Const(n, ls), args) if n == quotLiftName && args.size >= 6 =>
  val quotArg = whnf(args(5))  // Reduce the quotient argument first
  quotArg match {
    case Apps(Const(mk, _), mkArgs) if mk == quotMkName =>
      // Apply function to unwrapped value
      Some(Apps(args(3), mkArgs.last :: args.drop(6)))
    case _ => None  // Still stuck
  }
```

### Phase 3: Improve Proof Irrelevance Application
**Estimate**: Moderate complexity

1. Move proof irrelevance check earlier in `checkDefEq`:
   ```scala
   // After whnf but before structural comparison:
   if (isPropSafe(infer(e1)) && isPropSafe(infer(e2))) {
     // Compare types only
     return checkDefEq(infer(e1), infer(e2))
   }
   ```

2. Add `isPropSafe` that handles inference failures gracefully

### Phase 4: Cheap Projection Mode
**Estimate**: Low complexity

Add parameter to control projection reduction aggressiveness:

```scala
def whnf(e: Expr, cheapProj: Boolean = false): Expr = {
  // If cheapProj, don't unfold definitions when reducing projections
}
```

This matches Lean 4's behavior for `whnf_core(e, cheap_rec, cheap_proj)`.

### Phase 5: Decidable Instance Debugging
**Estimate**: Investigation needed

For the 18 decidability failures:
1. Trace a specific failure (e.g., `BitVec.divRec_succ'`)
2. Find where `ite` stops reducing
3. Check if decidable instance has proper reduction rules
4. May need to add special handling for `Decidable.decide`

---

## Files to Modify

| File | Changes |
|------|---------|
| `typechecker.scala` | Add tryEtaStruct, improve proof irrelevance, fix Quot reduction |
| `quotient.scala` | May need to adjust reduction rule setup |
| `environment.scala` | Track single-constructor types for eta-struct |

---

## Verification

### Test Progression
1. **Conformance tests**: Must remain at 19/19 pass
2. **Unit tests**: Must remain passing (~74 tests)
3. **Init failures**: Track reduction from 328 → 0

### Incremental Testing
After each phase:
```bash
sbt stage
JAVA_HOME=/opt/homebrew/opt/openjdk ./target/universal/stage/bin/trepplein -J-Xss16m /tmp/init.lean4export 2>&1 | tee /tmp/phase-N.log | tail -50
grep -c "wrong type:" /tmp/phase-N.log
```

### Target
- Phase 1 (Eta-struct): Expect ~100-150 fewer failures
- Phase 2 (Quot): Expect ~25 fewer failures
- Phase 3 (Proof irrelevance): Expect ~50-100 fewer failures
- Phase 4-5: Mop up remaining

### Final Goal
- 0 failures on Init export
- `canBypass` remains `false` - no bypass needed
- Matches behavior of nanoda_lib and Lean 4 kernel

---

## Risk Assessment

- **Eta-struct**: May require tracking single-constructor types in environment
- **Quot**: Straightforward change, low risk
- **Proof irrelevance**: Care needed to avoid infinite loops (checking type equality recursively)
- **Decidability**: May reveal deeper issues with instance reduction

The goal is correctness matching the reference implementations, not shortcuts.
