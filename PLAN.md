# Trepplein Type Checker — Status and Plan

## Current Status

| Metric | Value | Notes |
|--------|-------|-------|
| Init library errors (nightly-2026-01-10) | **0** | ✅ |
| Init library errors (nightly-2026-01-23) | **0** | ✅ |
| trustExports bypasses | **0** | |

All declarations in Init pass verification on both tested nightlies.

---

## Next Actions

No pending issues. Trepplein successfully verifies the entire Init library.

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
