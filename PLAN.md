# Plan: Zero Errors, Zero Bypasses

## Current Status

| Metric | Value |
|--------|-------|
| Errors | **3** |
| Bypasses | **0** |
| Target | **0 errors, 0 bypasses** |

See `DEFECTS.md` for detailed documentation of resolved and open defects.

---

## Remaining Issue: UInt succMany (3 errors)

**Affected:** UInt16/32/64.succMany?_ofBitVec

**Problem:** `PProd.0 (Nat.rec ... n)` is stuck when `n` is large (65535, 4B, 18B). Computing `Nat.below` requires structural recursion on `n`, which is O(n).

**Root cause:** `Nat.below motive n` is computed via `Nat.rec`, producing a nested `PProd` structure. Extracting with `PProd.0` requires the full computation.

**Options:**
1. Native `PProd` projection on `Nat.below` pattern (recognize and compute directly)
2. Implement interpreter/VM for expensive computations
3. Accept as limitation for very large numbers

---

## Verification Command

```bash
sbt stage && \
JAVA_HOME=/opt/homebrew/opt/openjdk ./target/universal/stage/bin/trepplein \
  -J-Xss16m /tmp/init.lean4export 2>&1 | tee /tmp/test.log | tail -30
grep -c "wrong type" /tmp/test.log
```
