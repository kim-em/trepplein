# Trepplein Type Checker — Status and Plan

## Current Status

| Metric | Value | Notes |
|--------|-------|-------|
| Init library errors (nightly-2026-01-10) | **0** | ✅ |
| Init library errors (nightly-2026-01-23) | **0** | ✅ |
| Init library errors (nightly-2026-01-24) | **0** | ✅ |
| trustExports bypasses | **0** | |
| Conformance tests passing | **19/19** | ✅ All pass |

All declarations in Init pass verification. All conformance tests pass.

---

## Next Actions (Priority Order)

### P0: Soundness Issues — RESOLVED ✅

Both `RecursorRhsUnchecked` and `WrongUniverse` conformance tests now pass:
- Recursor rule RHS is type-checked (rejects corrupted RHS like returning Prop)
- Universe params are validated against the inductive type

### P1: Potential Soundness Concerns — VERIFIED ✅

3. **inProgressPairs cycle detection** — VERIFIED SOUND
   - Returns `IsDefEq` optimistically when a cycle is detected during checking
   - This is sound: the optimistic return only affects inner recursive calls,
     the final cached result always comes from checkDefEqCore
   - If expressions truly differ, a structural mismatch will be found elsewhere
   - Similar to Lean 4's equiv_manager approach
   - Documentation improved in code comments

4. **Platform dependency** — DOCUMENTED
   - `USize`/`ISize` assumes 64-bit platform (platformBits = 64)
   - This is a fundamental property shared with Lean 4 itself
   - Export files don't specify platform, so assumption is necessary
   - Documentation added in code comments (typechecker.scala:873-883)

### P2: Code Quality

5. **Refactor TypeChecker class** (~2100 lines after cleanup)
   - Extract `NativeReduction` module
   - Extract `StructureExpansion` module
   - Extract name constants to separate object

6. **Consolidate extraction logic** — DEFERRED (architectural constraint)
   - `LiteralReduction.extractNatLit` vs `TypeChecker.extractNatValue`
   - Duplication is intentional: LiteralReduction can't use whnf (would cause infinite recursion)
   - TypeChecker versions use whnf, LiteralReduction versions work on already-reduced forms
   - Low priority: current design works correctly

7. ~~**Remove dead debug code**~~ ✅ DONE
   - Removed investigation-specific debug code (~80 lines)
   - Remaining debug code is guarded by flags (`eagerReduceDebug`, `ctorIdxDebug`)

8. ~~**Fix mutable global state**~~ ✅ DONE (literal.scala:20-27)
   - Changed `var` to `val` for Config flags (enableNatReduction, enableStringReduction, debugHMod)
   - To debug, change constants and rebuild

### P3: Robustness

9. **Add resource limits** (partial)
   - ~~Memory cap for caches~~ ✅ DONE
     - Added `maxCacheSize = 500000` to TypeChecker.Limits
     - whnfCache, defEqCache, levelDefEqCache, instantiationCache now cleared when exceeding limit
   - Timeout for type checking individual declarations (TODO)

10. ~~**Add axiom filtering**~~ ✅ DONE
    - Added `--permitted-axioms ax1,ax2,...` option to restrict allowed axioms
    - Added `--reject-unpermitted-axioms` to fail (vs warn) on unpermitted axioms
    - Tracks axioms via `PreEnvironment.axioms: Set[Name]`
    - Standard Lean axioms: `propext,Classical.choice,Quot,Quot.ind,Quot.lift,Quot.mk,Quot.sound`
    - Other axioms in Init: `Lean.ofReduceBool,Lean.ofReduceNat,Lean.trustCompiler,sorryAx`

11. **Improve error messages** (partial)
    - ~~Better parser error messages for malformed exports~~ ✅ DONE
      - Parser now includes line numbers in all error messages
      - Example: "line 3: unknown expression type '#EX'"
    - Add trace for why two expressions aren't definitionally equal (TODO)

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

---

## Architecture Notes

### Caches

| Cache | Location | Bounded? |
|-------|----------|----------|
| whnfCache | typechecker.scala | Yes (maxCacheSize) |
| defEqCache | typechecker.scala | Yes (maxCacheSize) |
| levelDefEqCache | typechecker.scala | Yes (maxCacheSize) |
| instantiationCache | typechecker.scala | Yes (maxCacheSize) |

All caches are now bounded by `TypeChecker.Limits.maxCacheSize` (default 500,000 entries).
When a cache exceeds this size, it is cleared to prevent unbounded memory growth.

### Reduction Rule Matching

`ReductionMap.apply` (reduction.scala:100-110) does linear search through rules for a constant. Could be slow if many rules exist for one constant.

### Duplication

| Function | literal.scala | typechecker.scala |
|----------|---------------|-------------------|
| extractNatLit | ✓ (line 53) | ✓ (extractNatValue, line 255) |
| extractIntLit | ✓ (line 214) | ✓ (extractIntValue, line 1033) |
| mkIntLit | ✓ (line 233) | ✓ (mkIntExpr, line 1200) |

---

## Test Coverage

### Conformance Tests (from nanoda_lib) — ALL PASS ✅

| Test | Status | Notes |
|------|--------|-------|
| Empty | ✅ | |
| Sexpr, Sexpr1-3 | ✅ | Nested/mutual recursors |
| Cycle1 | ✅ | Direct cycle detected |
| CycleMutual1 | ✅ | Mutual cycle detected |
| CycleOpaque1-3 | ✅ | Opaque cycle detected |
| Nonpositive1-2 | ✅ | Non-positive occurrence detected |
| AxiomNotAllowed0-2 | ✅ | Forward references / axiom checks |
| BadSemver | ✅ | Invalid version rejected |
| PpDoubleFrench | ✅ | Pretty printing test |
| RecursorRhsUnchecked | ✅ | Corrupted RHS rejected |
| WrongUniverse | ✅ | Corrupted universe rejected |

### Missing Test Coverage

- No property-based tests (QuickCheck/ScalaCheck)
- No Mathlib verification tests
- No stress tests for resource limits
