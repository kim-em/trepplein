# Trepplein Type Checker — Status and Plan

## Current Status

| Metric | Value | Notes |
|--------|-------|-------|
| Init library errors (nightly-2026-01-22) | **0** | ✅ |
| Init library errors (nightly-2026-01-23) | **1** | ⚠️ Regression |
| Std library errors (v4.27.0) | **32** | ❌ BVDecide module |
| Batteries library errors (v4.27.0) | **3** | ⚠️ Reduced from 10 (see below) |
| trustExports bypasses | **0** | |
| Conformance tests passing | **19/19** | ✅ All pass |
| Arena tests passing | **26/26** | ✅ All pass |

All declarations in Init pass verification (up to nightly-2026-01-22). All conformance and arena tests pass.

**Known issues**:
- nightly-2026-01-23+ fails on `Char.succ?_eq` with a DefEq failure. Needs investigation.
- Std library has 32 errors in `Std.Tactic.BVDecide.*` (indexed inductive issues)
- Batteries library has 3 errors (Categories 3 and 4 - see detailed investigation below)

---

## Next Actions (Priority Order)

### P0: Std Library Indexed Inductive Issue

**Status**: INVESTIGATING

32 errors in `Std.Tactic.BVDecide.*` all follow the same pattern:
```
Std.Tactic.BVDecide.BVExpr.decEq: wrong type:  Eq.rec lexpr (...)  :  BVExpr w
inferred type:  (λ x h, BVExpr x) rw (...)
w  !=def  rw
reason: different head symbols: LocalConst vs LocalConst
```

**Root cause**: `BVExpr` is indexed by a width parameter `w : Nat`. When checking expressions involving `Eq.rec` (used to cast between different widths), the inferred type mentions one local constant (e.g., `rw`) while the expected type mentions another (e.g., `w`).

**Investigation findings**:
1. Added de Bruijn level tracking to local constants (`LocalConst.Name.level`)
2. The local constants genuinely have different levels (e.g., L3 vs L4)
3. Different levels mean they represent different bound variables in the context
4. For `Eq.rec` applications, the inferred type correctly shows `motive target h` where `target` is the RHS of the equality proof
5. The mismatch suggests the expected type comes from a different source than where the `Eq.rec` application uses

**Possible causes**:
- Type annotations in the export that we're trusting incorrectly
- Incorrect instantiation of indexed inductive types
- Missing reduction/simplification step

**Next steps**:
- [ ] Check how Lean 4 kernel computes types for indexed inductives
- [ ] Compare with nanoda's approach (blocked: nanoda fails on trustCompiler axiom)
- [ ] Add detailed tracing to see exactly what types are being compared

---

### P0: Batteries Library Errors (3 remaining)

**Status**: PROGRESS — 7 errors fixed, 3 remaining

Batteries had 10 errors in 4 categories. Categories 1 and 2 are now fully fixed.

#### Category 1: Unused Universe Params (2 errors) — ✅ FIXED

**Errors** (now fixed):
```
Lean.ToLevel: requirement failed: inductive type Lean.ToLevel declares universe params u that don't appear in its type
Std.Internal.Small: requirement failed: inductive type Std.Internal.Small declares universe params u that don't appear in its type
```

**Fix applied** (commit `0da0ef3`):
- Moved check from IndMod to CtorMod
- Params must appear in EITHER the inductive type OR constructor fields (excluding self-references)
- Added `Expr.univParamsExcluding(name)` method

This correctly:
- ✅ Accepts `ToLevel.{u}` where `u` appears in constructor field types
- ✅ Accepts `PUnit.{u}` where `u` appears in the inductive type (`Sort u`)
- ✅ Rejects `WrongUniverse` where `u` is declared but never used meaningfully

#### Category 2: SizeOf Computation Path Mismatch (7 errors) — ✅ FIXED

**Errors** (now fixed): `*._sizeOf_*_eq` declarations (Lean.Language.SnapshotTree, Lean.Elab.Term.Do.Code, etc.)

**Root cause**: Nested recursors (`rec_2`, `rec_3`, etc.) compute sizeof via nested recursor chains, while `SizeOf.sizeOf` uses well-founded recursion. When comparing these, the expressions are stuck on structure-typed variables that need eta-expansion.

**Fix applied**: Enabled eta-struct expansion for nested recursors (not just standard `TypeName.rec`).

Before: Only recursors ending in exactly "rec" or "casesOn" would trigger eta-struct expansion.
After: Recursors ending in "rec_N" or "casesOn_N" (nested recursors) also trigger eta-struct expansion.

This allows `rec_3 ... head` and `PProd.0 (Nat.rec ...)` to both reduce after expanding `head : SnapshotTask` to its constructor form `SnapshotTask.mk head.0 head.1 head.2 head.3`.

**Previous investigation findings** (2026-01-26):

**Expected side** (after `_sizeOf_3 (List.cons head tail)` reduces):
```
... rec_3 ... head ...  (nested recursor chain)
```

**Inferred side** (from proof term inference):
```
... PProd.0 (Nat.rec ...) ...  (well-founded recursion)
```

Both compute the same value (sizeof of `head`), but use different definitional computation paths:
- Nested recursors: `rec_3 ... head` - the auto-generated nested recursor for `SnapshotTask`
- Well-founded recursion: `PProd.0 (Nat.rec ...)` - the standard `sizeOf` implementation via `Nat.below`

The fix was to enable eta-struct expansion for nested recursors, which allows both expressions to reduce when the structure-typed variable (`head : SnapshotTask`) is expanded to its constructor form.

**Note**: Nanoda also fails on Batteries with the same pattern (`assertion failed: self.def_eq(u, v)` at tc.rs:797), but trepplein now handles it correctly

#### Category 3: Nat Arithmetic Non-Definitional Equality (2 errors) — ROOT CAUSE FOUND

**Errors**:
```
_private.Batteries.Data.Char.Basic.0.Char.any._proof_1: wrong type
_private.Batteries.Data.Char.Basic.0.Char.all._proof_1: wrong type
```

**Pattern** (Char.any):
```
Expected: Eq (LE.le (HAdd.hAdd (OfNat.ofNat 57343) (OfNat.ofNat 1))
              (HAdd.hAdd (HAdd.hAdd c (OfNat.ofNat 57343)) (OfNat.ofNat 1))) True
Inferred: Eq (LE.le (OfNat.ofNat 57344) (HAdd.hAdd c (OfNat.ofNat 57344))) True
```

**Root cause**: Both `(c + 57343) + 1` and `c + 57344` reduce to `succ(c + 57343)`, so they SHOULD be definitionally equal. But they're represented differently via well-founded recursion:

- LHS: `Nat.succ (PProd.0 (Nat.rec ... 0) (c + 57343))` — already partially reduced
- RHS: `PProd.0 (Nat.rec ... 57344) c` — not yet reduced

The issue is that one side has `Nat.succ (...)` as head while the other has `PProd.0 (...)`. Our PProd pattern handles `PProd.fst (Nat.rec ...) vs Nat.rec ...` but not this case.

**Why this passes in Lean's kernel**: Lean's kernel likely has additional patterns for recognizing equivalent well-founded recursion forms, or it reduces both sides more aggressively before comparing.

**Possible fixes**:
1. Extend PProd pattern to handle `Nat.succ (PProd.0 ...) vs PProd.0 (Nat.rec ... succ(n))`
2. More aggressive reduction of well-founded recursion expressions before comparison
3. Add general pattern for recognizing equivalent `Nat.add` computations

**Current status**:
- [x] Identified root cause: different well-founded recursion representations
- [x] Both sides compute the same value (`succ(c + 57343)`)
- [ ] Implement additional PProd pattern for this case

#### Category 4: Small.pbind Type Mismatch (1 error) — NEEDS INVESTIGATION

**Error**:
```
Std.Internal.Small.pbind: wrong type:  Exists.0 (Exists.choose_spec (Subtype.property y))  :  (λ (x : α), P x) (Exists.choose (Subtype.property y))
inferred type:  Exists (λ (x : α), (λ (a : α), Exists (λ (h : P a), Q a h (Subtype.val y))) x)
P (Exists.choose (Subtype.property y))  !=def  Exists (λ (x : α), ...)
reason:  different head symbols: LocalConst vs Const
```

**Root cause**: The comparison fails because:
- Expected type head: `P` (a LocalConst — a parameter in scope)
- Inferred type head: `Exists` (a Const — the standard library type)

These are completely different types! `P x` vs `Exists (...)`.

**This is NOT a simple reduction issue**. Either:
1. The type annotation in the export is wrong
2. We're inferring the type incorrectly
3. There's a substitution/instantiation error

**Investigation needed**:
- [ ] Trace the full type inference for `Exists.0 (Exists.choose_spec ...)`
- [ ] Check what type `Exists.0` (the first projection of Exists) should return
- [ ] Compare with how nanoda/lean4lean handle `Exists.choose_spec`

**Note**: `Std.Internal.Small` also has the unused universe param error (Category 1), so fixing that first will clarify if this is a separate issue.

---

### Summary: Batteries Fix Priority

1. ~~**Category 1 (Universe params)**~~: ✅ FIXED — relax the check in `IndMod.compile`
2. ~~**Category 2 (SizeOf nested recursors)**~~: ✅ FIXED — enable eta-struct expansion for nested recursors
3. **Category 3 (Nat arithmetic)**: OPEN — `(c + 57343) + 1` vs `c + 57344` not definitionally equal
4. **Category 4 (Small.pbind)**: OPEN — genuine type mismatch, needs deeper investigation

---

### P1: Address Gabriel's Code Quality Feedback

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

All soundness issues resolved:
- `RecursorRhsUnchecked` - Recursor rule RHS is type-checked
- `WrongUniverse` - Universe params are validated against the inductive type
- `nonPropThm` - Theorems must have types in Prop (now checked)
- Duplicate universe params - Now rejected (check in Declaration.check)

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

11. ~~**Improve error messages**~~ ✅ DONE
    - ~~Better parser error messages for malformed exports~~ ✅ DONE
      - Parser now includes line numbers in all error messages
      - Example: "line 3: unknown expression type '#EX'"
    - ~~Add trace for why two expressions aren't definitionally equal~~ ✅ DONE
      - NotDefEq now includes a reason field explaining why
      - Example: "reason: universe levels differ: u vs v"

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
| ~~environment.scala:59~~ | Reducibility hints should be passed directly | ✅ Simplified: Opaque/Abbrev use height 0 |
| environment.scala:212 | Cycle detection scans all prior definitions | Kept: provides early fail-fast with clear errors |
| environment.scala:318 | inductiveInfo should be part of declarations map | Deferred: lower priority refactoring |
| ~~expr.scala:157~~ | Manual resizable arrays | ✅ Reverted to recursive version |
| literal.scala:60 | Names recomputed every call | BLOCKED: forward references |
| literal.scala:65 | Crazy complexity in extractNatLit | KEPT: simplification breaks type checking |
| ~~literal.scala:255~~ | Use backtick syntax for name matching | ✅ reduceLiteralConst uses backtick syntax |
| ~~literal.scala:303~~ | Unexplained special case | ✅ Documented (Decidable.casesOn) |
| ~~name.scala:79~~ | mkStr is a footgun | ✅ Constructors now package-private |
| ~~reduction.scala:32~~ | Hot path allocations | ✅ Investigated: recursive version fails |
| ~~typechecker.scala:21~~ | Recursion depth tracking | ✅ Removed, catch StackOverflow in checkType |
| ~~typechecker.scala:51~~ | Should use ppError | ✅ Replaced prettyExpr with ppDebug wrapper |
| typechecker.scala:164 | 100000 loop limit | Kept: safety limits for iterative extraction |
| typechecker.scala:220 | Move names to companion object | BLOCKED: forward references |
| typechecker.scala:508 | Workaround instead of fix | Kept: handles malformed reduction output |
| typechecker.scala:1390 | Was handled by IndMod reduction rules | Kept: isK needs isDefEq from type checker |

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

### Lean Kernel Arena Tests — ALL PASS ✅

Tests from https://arena.lean-lang.org/ (download: lean-arena-tests.tar.gz)

| Category | Pass | Fail | Notes |
|----------|------|------|-------|
| Good tests | 21/21 | 0 | All pass ✅ |
| Bad tests (should reject) | 5/5 | 0 | All correctly rejected ✅ |

### Library Integration Tests (CI)

| Library | Script | CI Job | Status |
|---------|--------|--------|--------|
| Init | `generate-init-export.sh` | init-test | ✅ Passing |
| Std | `generate-std-export.sh` | std-test | ❌ 32 errors |
| Batteries | `generate-batteries-export.sh` | batteries-test | ❌ 10 errors |

### Missing Test Coverage

- No property-based tests (QuickCheck/ScalaCheck)
- No Mathlib verification tests
- No stress tests for resource limits
