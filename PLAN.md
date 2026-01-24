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

### P0: Address Gabriel's Code Quality Feedback

Working through Gabriel's PR review comments in order of impact:

1. ~~**Move names to companion objects**~~ — BLOCKED (literal.scala:60, typechecker.scala:220)
   - Currently recomputing interned names on every call
   - Attempted refactoring but hit issues with:
     - Forward references between val declarations (OfNatOfNatName uses OfNatName)
     - Pattern matching behavior differences when using object-level vs local vals
   - Needs more investigation or alternative approach (lazy vals? careful reordering?)

2. ~~**Remove recursion depth tracking**~~ ✅ DONE (typechecker.scala:21)
   - Gabriel: "absolutely no point in doing this in Scala"
   - Removed ~50 lines of depth tracking code
   - Now catches StackOverflowError in checkType and wraps with context

3. ~~**Revert hot path allocations**~~ ✅ INVESTIGATED (reduction.scala:32)
   - Attempted to revert to original recursive pattern matching
   - Recursive version causes infinite loop/exponential behavior on Init library
   - Kept iterative version (ArrayBuffer allocation is necessary for correctness)

4. ~~**Fix Name.mkStr footgun**~~ ✅ DONE (name.scala:79)
   - Made Str/Num constructors package-private (`private[trepplein]`)
   - Prevents external code from bypassing interning

### P1: Soundness Issues — RESOLVED ✅

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

## Gabriel's PR Review (gebner/trepplein#4)

Gabriel's main concerns from PR review:

### High-Level Issues

1. ~~**"Trusted exports" / type-incorrect terms**~~ ✅ RESOLVED
   - `trustExports` bypasses removed (now 0 bypasses)
   - All declarations properly type-checked

2. **Mixed functionality with optimizations**
   - Get functionality working first, benchmark later
   - Some "optimizations" are counterproductive

3. **Inductive checking design** (architectural)
   - Parser should reassemble split export declarations into single IndMod
   - Single modification can verify recursors match expected form
   - Currently trusts export format too much

4. **Native implementation type-checking**
   - Differs from Lean 4 kernel approach
   - Needs justification or alignment with Lean 4 code

### Inline Comments

| File | Issue | Status |
|------|-------|--------|
| ~~CLAUDE.md:32~~ | trustExports flag | ✅ Removed |
| ~~typechecker.scala:293~~ | Debug code | ✅ Guarded by `eagerReduceDebug` |
| ~~typechecker.scala:1012~~ | Debug code | ✅ Guarded by `ctorIdxDebug` |
| ~~benchmark.sh~~ | sbt startup overhead | ✅ CLAUDE.md documents staged binary |
| environment.scala:59 | Reducibility hints should be passed directly | TODO |
| environment.scala:212 | "Optimized" code scans all prior definitions | TODO: remove |
| environment.scala:318 | Should be part of declarations map | TODO |
| expr.scala:157 | Manual resizable arrays | TODO: use bigger stack instead |
| literal.scala:60 | Names recomputed every call | BLOCKED: forward references |
| literal.scala:65 | Crazy complexity in extractNatLit | TODO: simplify to match Lean 4 |
| literal.scala:255 | Use backtick syntax for name matching | TODO |
| literal.scala:303 | Unexplained special case | TODO: document or remove |
| ~~name.scala:79~~ | mkStr is a footgun | ✅ Constructors now package-private |
| ~~reduction.scala:32~~ | Hot path allocations | ✅ Investigated: recursive version fails |
| ~~typechecker.scala:21~~ | Recursion depth tracking | ✅ Removed, catch StackOverflow in checkType |
| typechecker.scala:51 | Should use ppError | TODO |
| typechecker.scala:164 | 100000 loop limit | TODO: review necessity |
| typechecker.scala:220 | Move names to companion object | BLOCKED: forward references |
| typechecker.scala:508 | Workaround instead of fix | TODO: fix reduction code |
| typechecker.scala:1390 | Was handled by IndMod reduction rules | TODO: review |

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
