# Plan: Implement `eagerReduce` Support

## Problem

`Nat.mul_add_div` and similar declarations fail type checking because they use `native_decide` proofs wrapped in `eagerReduce`. Trepplein doesn't recognize `eagerReduce` as a special form requiring aggressive reduction.

## How Lean 4 Kernel Handles `eagerReduce`

From `/tmp/lean4/src/kernel/type_checker.cpp`:

1. **Detection** (lines 158-161):
   ```cpp
   static bool is_eager_reduce(expr const & e) {
       return is_const(get_app_fn(e), *g_eager_reduce) && get_app_num_args(e) == 2;
   }
   ```

2. **Setting mode** (lines 168-176):
   ```cpp
   if (is_eager_reduce(app_arg(e))) {
       flet<bool> scope(m_eager_reduce, true);
       if (!is_def_eq(a_type, d_type)) {
           throw app_type_mismatch_exception(...);
       }
   }
   ```

3. **Aggressive reduction** (lines 969-975, 1057-1060):
   - When `m_eager_reduce` is true, `reduce_nat` is called even with free variables
   - When comparing `t =?= Bool.true`, fully reduce `t` and check if result is `Bool.true`

## Implementation Plan for Trepplein

### Step 1: Add `eagerReduce` name constant

In `typechecker.scala`, add:
```scala
private val eagerReduceName = Name.mkStr(Name.Anon, "eagerReduce")
```

### Step 2: Detect `eagerReduce` in `checkType`

Before checking `checkType(e, ty)`, check if `e` is of the form `eagerReduce _ arg`:
```scala
def checkType(e: Expr, ty: Expr): Unit = {
  e match {
    case Apps(Const(n, _), List(_, arg)) if n eq eagerReduceName =>
      // Enable eager reduction mode for this type check
      withEagerReduce {
        checkType(arg, ty)
      }
    case _ =>
      // Normal type checking
      ...
  }
}
```

### Step 3: Add `eagerReduce` flag to TypeChecker

Add a mutable flag or thread through a parameter:
```scala
private var eagerReduceMode: Boolean = false

private def withEagerReduce[T](f: => T): T = {
  val old = eagerReduceMode
  eagerReduceMode = true
  try f finally eagerReduceMode = old
}
```

### Step 4: Modify `checkDefEqCore` for `Bool.true` comparisons

In `checkDefEqCore`, add special handling when one side is `Bool.true`:
```scala
// In checkDefEqCore:
if (eagerReduceMode) {
  // When comparing with Bool.true, fully reduce the other side
  if (fn2 == BoolTrue && as2.isEmpty) {
    val e1Reduced = whnf(e1_0)  // Fully reduce
    return reqDefEq(e1Reduced == boolTrue, e1, e2)
  }
  if (fn1 == BoolTrue && as1.isEmpty) {
    val e2Reduced = whnf(e2_0)
    return reqDefEq(e2Reduced == boolTrue, e1, e2)
  }
}
```

### Step 5: More aggressive reduction in `whnf` when `eagerReduceMode`

In `whnfCore`, when `eagerReduceMode` is true:
- Continue reducing even when expressions would normally be considered stuck
- Try all reduction rules more aggressively

## Testing

1. Create a minimal export file with a `native_decide` proof
2. Verify trepplein handles it correctly
3. Test on full Init export

## Notes

- This is a correctness issue, not just performance
- Without `eagerReduce` support, any declaration using `native_decide` will fail
- The fix should not affect performance of non-`eagerReduce` terms
