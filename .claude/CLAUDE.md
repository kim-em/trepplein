# Trepplein - Independent Type Checker for Lean 4

## Document Split: CLAUDE.md vs PLAN.md

**This file (CLAUDE.md)** contains timeless truths:
- Project philosophy and principles
- Build/test commands
- Reference implementations
- Export format

**PLAN.md** contains evolving knowledge:
- Current status (error counts, etc.)
- Priority-ordered next actions
- Known issues and investigation steps
- Historical context

**If the user says "start work" or similar, begin by reading `PLAN.md`** and work on the highest-priority action listed there.

**Update `PLAN.md` as you work:**
- Mark items complete when done
- Add new issues as you discover them
- Refine next steps based on what you learn
- Leave clear instructions for the next agent

The goal is that any new Claude agent can read PLAN.md and immediately know what to work on, without needing prior context.

---

## Project Goals

Trepplein is an **independent type checker** for Lean 4's kernel. Its purpose is to provide a fully reliable, alternative implementation that can verify Lean 4 proofs without trusting Lean's own kernel.

### Core Principles

1. **No Cheating**: Every declaration must be verified correctly according to the type theory. If something doesn't type-check, we must fix the actual reduction/inference logic, NOT add workarounds or special cases to skip failures.

2. **Independent Implementation**: The value of trepplein is that it's a separate implementation. If we add hacks to make things pass that shouldn't, we lose the security guarantees.

3. **Full Kernel Coverage**: We must implement all kernel features:
   - Definitional equality with proper reduction
   - Universe polymorphism
   - Inductive types and recursors
   - Quotient types
   - Proof irrelevance
   - Eta-struct expansion
   - Structural comparison of stuck terms

---

## CRITICAL: No Bypass Code

- **NEVER** add bypass conditions to skip failing checks
- **NEVER** re-enable `trustExports`
- **NEVER** "fix" a failure by adding special cases that skip verification

When a new failure appears, understand WHY it fails and implement the correct fix. Reference nanoda_lib and Lean 4 kernel for correct behavior.

---

## CRITICAL: No "Trust It Works" Optimizations

**NEVER implement an optimization that assumes a computation would succeed without actually performing it.**

This includes:
- Trusting that `native_decide` proofs are correct without reducing them
- Trusting that `eagerReduce` computations would produce `Bool.true`
- Skipping expensive computations because "Lean already verified it"
- Any form of "if the proof has this shape, assume it's valid"

The ENTIRE POINT of an independent type checker is to independently verify. If verification is too slow, the correct responses are:
1. **Optimize the reduction engine** (better algorithms, native Nat ops, etc.)
2. **Accept that some proofs take time** to verify
3. **Report the limitation** to the user

The WRONG response is to pretend verification happened when it didn't. This defeats the security purpose of the project.

**If you find yourself writing code that "trusts" something without verifying it, STOP and reconsider.**

---

## Building and Testing

### Compile and Stage (do this after code changes)

```bash
sbt stage
```

This compiles and creates a standalone executable at `./target/universal/stage/bin/trepplein`.

### Running Trepplein

**ALWAYS use the staged executable, NOT `sbt run`:**

```bash
# Fast - directly calls java, no sbt overhead
./target/universal/stage/bin/trepplein /tmp/init.lean4export

# With increased stack for large files (16m needed for Init library)
./target/universal/stage/bin/trepplein -J-Xss16m /tmp/init.lean4export
```

**NEVER use `sbt run`** - it adds 10-20 seconds of sbt startup overhead on every invocation.

### CRITICAL: Capture Output to Files

**NEVER run trepplein multiple times to extract different parts of the output.** Instead:

1. **First run: capture to file AND limit what you see:**
   ```bash
   JAVA_HOME=/opt/homebrew/opt/openjdk ./target/universal/stage/bin/trepplein -J-Xss16m /tmp/init.lean4export 2>&1 | tee /tmp/trepplein-run.log | tail -20
   ```

2. **Then extract other parts from the saved file:**
   ```bash
   grep "wrong type" /tmp/trepplein-run.log
   head -50 /tmp/trepplein-run.log
   ```

3. **If you need to re-examine the output, use the file - don't re-run.**

### Verification

**Quick check (after `sbt stage`):**
```bash
./target/universal/stage/bin/trepplein -J-Xss16m /tmp/init.lean4export \
  2>&1 | tee /tmp/trepplein-run.log | tail -30
grep -c "wrong type" /tmp/trepplein-run.log  # Should be 0
```

**With error detection (slower, uses sbt):**
```bash
./run-trepplein.sh /tmp/init.lean4export
```

---

## Debugging Reduction Failures

When something doesn't reduce properly:
1. Use export analysis tools to trace the definition chain
2. Check if all intermediate definitions have reduction rules
3. Verify recursor rules are generated correctly
4. Trace the actual whnf computation to find where reduction stops

---

## Reference Type Checkers

### nanoda_lib (Rust)
An independent Lean 4 type checker. **The gold standard for correct behavior.**

```bash
cd /tmp && git clone https://github.com/ammkrn/nanoda_lib.git
cd nanoda_lib && cargo build --release

cat > /tmp/check_config.json << 'EOF'
{
    "export_file_path": "/absolute/path/to/export",
    "use_stdin": false,
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "print_success_message": true
}
EOF

/tmp/nanoda_lib/target/release/nanoda_bin /tmp/check_config.json
```

### Lean 4 Kernel (C++)
Located at `/tmp/lean4/src/kernel/`. Key files:
- `type_checker.cpp` - Main type checking logic
- `type_checker.h` - `try_eta_struct_core`, `is_def_eq_core`

### lean4lean (Lean 4)
Independent checker written in Lean 4 itself.

---

## Export Format Quick Reference

```
# Version
2.0.0

# Names (index #NS parent string) or (index #NI parent number)
1 #NS 0 Foo        # name 1 = "Foo"
2 #NS 1 bar        # name 2 = "Foo.bar"

# Levels (index #Ux ...)
1 #UP 3            # level 1 = Param(name 3)
2 #US 1            # level 2 = Succ(level 1)

# Expressions (index #Ex ...)
0 #ES 0            # expr 0 = Sort(level 0) = Prop
1 #EC 1            # expr 1 = Const(name 1, no levels)
2 #EA 1 0          # expr 2 = App(expr 1, expr 0)
3 #EL #BD 2 0 1    # expr 3 = Lam(name 2, expr 0, expr 1)
4 #EP #BD 2 0 1    # expr 4 = Pi(name 2, expr 0, expr 1)
5 #EV 0            # expr 5 = Var(0)

# Declarations
#IND name type isRefl isRec numNested numParams numIndices numInds indNames... numCtors ctorNames... uparams...
#CTOR name type inductName cidx numParams numFields uparams...
#REC name type numInds indNames... numParams numIndices numMotives numMinors numRules ruleIdxs... isK uparams...
#DEF name type value hints uparams...
#THM name type value uparams...
#AX name type uparams...
```
