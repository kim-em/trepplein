# Plan: Zero Errors, Zero Bypasses

## Current Status

| Metric | Value |
|--------|-------|
| Errors | **5** |
| Bypasses | **0** |
| Target | **0 errors, 0 bypasses** |

See `DEFECTS.md` for detailed documentation of resolved and open defects.

---

## Investigation Priority

Ordered by likelihood of being a fixable bug vs fundamental limitation:

### 1. String.toByteArray_empty (OPEN-3)

**Why first:** Type mismatch `Type 0 !=def List α` suggests a bug in type inference or reduction.

**Investigation plan:**
- Trace the full reduction of both sides
- Check List.nil type parameter handling
- Look for universe level issues

### 2. System.Platform.numBits_eq (OPEN-2)

**Why second:** Platform-dependent, but might have a reasonable solution.

**Options:**
1. Add `--platform-bits=64` configuration flag
2. Document as platform-dependent limitation

### 3. UInt succMany (OPEN-1, 3 errors)

**Why last:** Genuinely expensive computation (O(n) for large n).

**Options:**
1. Implement VM/interpreter for expensive computations
2. Native `PProd` projection on `Nat.below` pattern
3. Accept as limitation for very large numbers

---

## Next Actions

1. Investigate String.toByteArray_empty type mismatch
2. Add platform configuration for numBits_eq
3. Consider solutions for UInt succMany

---

## Verification Command

```bash
sbt stage && \
JAVA_HOME=/opt/homebrew/opt/openjdk ./target/universal/stage/bin/trepplein \
  -J-Xss16m /tmp/init.lean4export 2>&1 | tee /tmp/test.log | tail -30
grep -c "wrong type" /tmp/test.log
```
