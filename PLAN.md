# Trepplein Type Checker — Status and Plan

## Current Status

| Metric | Value |
|--------|-------|
| Init library errors | **0** |
| trustExports bypasses | **0** |

All 50,502 declarations in Init pass verification with `trustExports = false`.

---

## Next Actions (Priority Order)

### 1. Investigate PProd Pattern Legitimacy
**File:** `typechecker.scala:515-572`

This pattern claims definitional equality based on arithmetic (`k + 1 == n`), not reduction:

```scala
case (Proj(tn1, idx1, s1), Const(cn2, ls2))
  if tn1 == PProdName && idx1 == 0 && cn2.toString.contains("Nat.rec") =>
```

**To investigate:**
1. Check Lean 4 kernel (`/tmp/lean4/src/kernel/type_checker.cpp`) for similar patterns
2. Check nanoda_lib for how it handles `Nat.below` / well-founded recursion
3. Find which declarations trigger this pattern: add `println(s"[PPROD] $debugCurrentDecl")` and run on Init
4. Determine if this is semantically correct or a hack that should be removed

**Outcome:** Either justify with kernel reference, or remove and fix properly.

### 2. Replace String-Based Name Matching
**Files:** `typechecker.scala:527, 529, 551, 553, 2009-2011, 2523`

Replace fragile patterns like:
```scala
cn2.toString.contains("Nat.rec")  // BAD
```
With proper Name comparison using the existing interned name constants.

### 3. Fix Silent Exception Swallowing
**File:** `environment.scala:385-392`

Change `case _: Exception =>` to catch only specific expected exceptions.

### 4. Remove Dead trustExports Code
**Files:** `typechecker.scala:2439-2456, 2573-2580, 2611-2615, 2815-2835`

Delete the bypass code paths entirely since `trustExports` is always false.

---

## Other Issues (Lower Priority)

### Eager Reduction Depth Limit
**File:** `typechecker.scala:2306-2309`

```scala
if (depth > 1000) return whnfCore(e)(Transparency.all)  // Returns partial!
```

**Fix:** Throw error instead of returning partial result.

### Platform Bits Hardcoded
**File:** `typechecker.scala:839`

```scala
private val platformBits: Int = 64  // Wrong on 32-bit platforms
```

**Fix:** Document as assumption or make configurable.

---

## Code Quality Issues (Non-Urgent)

### Duplicated Cycle-Checking
**File:** `environment.scala:84-126` vs `170-213`

Two nearly identical functions with one line difference.

### Debug Statements (70+)
Throughout `typechecker.scala` and `literal.scala`:
- `[STUCK-DEBUG]`, `[PROOF-IRR]`, `[EAGER]`, `[HPOW]`, etc.
- Hardcoded `debugCurrentDecl.contains("succMany")` check

### Global Mutable State
**File:** `literal.scala:18-20`

```scala
var enableNatReduction: Boolean = true
var enableStringReduction: Boolean = true
var debugHMod: Boolean = false
```

### Magic Numbers
- `maxRecursionDepth = 5000`
- `depth > 1000` (eager reduction)
- `nv < 10000` (Nat.casesOn limit)
- `maxIter = 100000`

---

## Resolved Defects (Historical)

| ID | Issue | Resolution |
|----|-------|------------|
| CRITICAL-1 | Stuck projection comparison | Added cycle detection with `inProgressPairs` |
| CRITICAL-2 | Eta-struct implementation | Create projections and check def-eq |
| CRITICAL-3 | Instance projection reduction | Implemented `expandEtaStruct` |
| CRITICAL-4 | Omega/Grind computation | Native `Nat.gcd` and `Int.natAbs` |
| CRITICAL-5 | Indexed recursor rules | Separate `numFixed` for LHS/RHS |
| CRITICAL-6 | String.toByteArray | Fixed to include UInt8 type args |
| CRITICAL-7 | Platform.getNumBits | Added special case for extern |
| CRITICAL-8 | Nat.below PProd pattern | Added semantic shortcut (see issues above) |

Progress: 6091 → 4420 → 647 → 429 → 388 → 29 → 24 → 6 → 5 → 4 → 3 → **0**

---

## Core Principle: No Cheating

Trepplein is an **independent type checker**. Its value comes from independently verifying Lean 4 proofs.

**We will NOT:**
- Add bypass conditions to skip failing checks
- Trust computations without performing them
- Accept type mismatches as "probably fine"

**We WILL:**
- Implement correct reduction rules
- Add missing native operations
- Fix bugs in type checking logic
- Document limitations honestly
