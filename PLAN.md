# Plan: Fix Remaining 24 Type Errors

## Current Status

After fixing CRITICAL-1 (stuck projections), CRITICAL-2 (eta-struct), and CRITICAL-3 (recursor major premise expansion), we have 24 remaining errors. This plan addresses each category.

---

## Error Categories

| Category | Count | Root Cause | Status |
|----------|-------|------------|--------|
| Omega/Grind proofs | 18 | Complex reduction chain with free variables | Investigating |
| BitVec succMany? | 3 | `UInt*.size` not reducing to literal | Pending |
| Platform.numBits_eq | 1 | Subtype projection on opaque | Pending |
| String.toByteArray_empty | 1 | Strange type error | Pending |
| WellFounded.fixF_eq | 1 | `Acc.rec` not reducing | Pending |

---

## Investigation Results

### Omega/Grind Proofs (18 errors)

**Initial hypothesis:** Missing `Bool.true` reduction shortcut.

**What we found:**
1. Added Bool.true reduction shortcut (matching Lean 4 and nanoda)
2. The shortcut only applies when there are NO free variables
3. These proofs HAVE free variables (`x`, `y` from universal quantifiers)
4. The reduction chain involves: `tidyConstraint` → `lowerBound` → `Option.rec` → `Bool.true`
5. The chain is stuck because computations contain `Nat.cast x` which depends on free variables

**Key insight:** These proofs work in Lean 4 kernel NOT because of the Bool.true shortcut, but because:
- The types being compared are both `Eq (sat' ...) Bool.true`
- Both `sat'` expressions should reduce to `Bool.true`
- But our `tidyConstraint` → `lowerBound` chain is getting stuck somewhere

**Debug findings:**
- `normalize?` IS reducing (unfolds to its body)
- `tidyConstraint` IS reducing (not appearing after whnf)
- Something in the reduction chain isn't completing

**Possible causes to investigate:**
1. `Constraint.lowerBound` not extracting from constructor form correctly
2. `Option.rec` not firing on the result of `lowerBound`
3. `tidyConstraint` producing a form that `lowerBound` can't handle

### BitVec succMany? (3 errors)

The comparison involves `UInt16.size` vs `OfNat.ofNat 65536`. These should be definitionally equal.

**To investigate:** Is `UInt*.size` defined as an opaque or a reducible definition?

### Platform.numBits_eq (1 error)

```
64 !=def Subtype.val (System.Platform.getNumBits Unit.unit)
```

Platform-dependent constant that should reduce to 64 on a 64-bit platform.

### String.toByteArray_empty (1 error)

Strange error showing `List.nil : Type 0` which is syntactically wrong. May be a parsing or export issue.

### WellFounded.fixF_eq (1 error)

`Acc.rec` not reducing. This involves nested inductives and K-like reduction.

---

## Next Steps

### Priority 1: Debug Omega Reduction Chain

Add targeted debug output to trace:
1. What `tidyConstraint` produces (should be `Constraint.mk ...`)
2. What `lowerBound` extracts from it (should be `Option.none` or `Option.some`)
3. Why `Option.rec` on that result doesn't fire

### Priority 2: Check UInt*.size Definitions

Look at how `UInt16.size`, `UInt32.size`, `UInt64.size` are defined in the export file.

### Priority 3: Investigate Other Errors

After fixing the 18 Omega errors, investigate the remaining 6 errors individually.

---

## Code Changes Made

### Bool.true Reduction Shortcut (Added)

Location: `typechecker.scala` lines 264-284

```scala
// Special case for decide proofs: if one side is Bool.true and other has no fvars,
// try full reduction. This is needed for proofs like `Eq.refl true : decide p = true`.
(fn1, fn2) match {
  case (Const(n1, _), _) if (n1 eq BoolTrueName) && !hasLocalConst(e2) =>
    val e2Full = whnf(e2)
    e2Full match {
      case Const(n, _) if n eq BoolTrueName => return IsDefEq
      case _ => ()
    }
  case (_, Const(n2, _)) if (n2 eq BoolTrueName) && !hasLocalConst(e1) =>
    val e1Full = whnf(e1)
    e1Full match {
      case Const(n, _) if n eq BoolTrueName => return IsDefEq
      case _ => ()
    }
  case _ => ()
}
```

**Note:** This matches Lean 4 kernel and nanoda, but doesn't help with Omega proofs because they contain free variables.

---

## Verification

```bash
sbt stage
JAVA_HOME=/opt/homebrew/opt/openjdk ./target/universal/stage/bin/trepplein \
  -J-Xss16m /tmp/init.lean4export 2>&1 | tee /tmp/test.log | tail -30
grep -c "wrong type" /tmp/test.log
```

**Current:** 24 errors
**Target:** 0 errors
