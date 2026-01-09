# Trepplein Type Checker Defects

This document catalogs known defects in trepplein's type checking, validated by comparison against three reference implementations:
- **lean4** (C++) — The official Lean 4 kernel at `/tmp/lean4/src/kernel/`
- **lean4lean** (Lean 4) — Independent checker at `/tmp/lean4lean/`
- **nanoda_lib** (Rust) — Independent checker at `/tmp/nanoda_lib/`

Each defect is marked with severity and includes specific code locations in both trepplein and the reference implementations.

---

## CRITICAL-1: `trustExports` Bypass Still Active

**Status:** ACTIVE - 439 bypasses occur during Init check

### Current Behavior
**Location:** `environment.scala:64, 133, 151, 322` and `typechecker.scala:1923`

Declarations are checked with `trustExports = true`, and the bypass IS triggered:

```scala
val canBypass = trustExports && (
  isStuckTerm(i_) || isStuckTerm(t_) ||
  hasLocalConst(t_) || hasLocalConst(i_)
)
```

During Init library checking, **439 type mismatches** are silently bypassed.

### Bypass Categories (from instrumentation)
| Category | Count | Description |
|----------|-------|-------------|
| `PProd.0 (Nat.rec ...)` | 225 | Projections on Nat recursors |
| `PProd.0 (List.rec ...)` | 66 | Projections on List recursors |
| Monad instances | 38 | Bind/Seq/Functor/Pure mismatches |
| Iterator types | 14 | Std.Iterators patterns |
| Eta-struct | 3 | PSigma.mk x.1 x.2 !=def x |
| Other | ~93 | Various patterns |

### Reference Implementation Behavior

**nanoda_lib**: No bypass at all. Terms either match or fail.

**Lean 4 kernel**: No bypass. Uses multiple strategies (eta-struct, proof irrelevance, structural comparison of stuck terms), then fails.

### Root Cause: Missing Features

1. **No eta-struct**: We don't implement `tryEtaStruct` for `S.mk x.1 x.2 ... = x`
2. **No stuck projection comparison**: We don't structurally compare stuck projections
3. **Instance normalization**: Monad/Applicative instances accessed through different paths

---

## CRITICAL-2: Missing Eta-Struct Implementation

**Status:** NOT IMPLEMENTED

### What's Missing
Lean 4's `try_eta_struct_core` (`type_checker.cpp:784`) handles:
```
PSigma.mk (PSigma.fst x) (PSigma.snd x) =def= x
```

We have no such implementation. Currently 3+ declarations hit this case and are bypassed.

### Fix Required
Implement `tryEtaStruct` in `checkDefEq`:
- For single-constructor types (tracked in `inductiveInfo`)
- Expand `x` to `S.mk x.1 x.2 ... x.n` using projections
- Compare structurally

---

## CRITICAL-3: Missing Stuck Projection Comparison

**Status:** NOT IMPLEMENTED

### What's Missing
When comparing `Proj(T, i, s1)` vs `Proj(T, i, s2)` where both are stuck (struct doesn't reduce to constructor), we should compare `s1 =def= s2`.

Currently we try to reduce, fail, then bypass.

### Evidence
291 bypasses involve `PProd.0 (Nat.rec ...)` or `PProd.0 (List.rec ...)` patterns.

---

## MEDIUM-1: Mutable Global State for Literal Reduction

**Location:** `literal.scala:12-13`

```scala
var enableNatReduction: Boolean = true
var enableStringReduction: Boolean = true
```

Reference implementations have no mutable state affecting reduction.

---

## MEDIUM-2: `unsafeUnchecked` Flag Exists

**Location:** `typechecker.scala:15-16`

Currently only used for pretty-printing, but API allows misuse.

---

## Summary Table

| ID | Severity | Issue | Status |
|----|----------|-------|--------|
| CRITICAL-1 | Critical | `trustExports` bypass active | 439 bypasses in Init |
| CRITICAL-2 | Critical | Missing eta-struct | Not implemented |
| CRITICAL-3 | Critical | Missing stuck projection comparison | Not implemented |
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

## Next Steps

1. **Implement eta-struct** - Should resolve ~3 bypasses and potentially help with others
2. **Implement stuck projection comparison** - Should resolve ~291 bypasses
3. **Investigate monad instance mismatches** - May require deeper typeclass handling
4. **Set `trustExports = false`** - After fixes, verify Init passes without bypasses
5. **Remove bypass code entirely** - Once no longer needed

See `REMAINING_ISSUES.md` for detailed analysis and implementation guidance.
