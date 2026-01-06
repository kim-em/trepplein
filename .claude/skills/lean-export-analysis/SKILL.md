---
name: lean-export-analysis
description: Analyze Lean 4 export files. Use when debugging trepplein type checking failures, investigating why expressions don't reduce, or exploring the structure of exported definitions.
allowed-tools: Bash, Read
---

# Lean 4 Export Analysis

This skill provides tools for analyzing Lean 4 export files when debugging the trepplein type checker.

## Tool Location

```
.claude/skills/lean-export-analysis/export-analysis.py
```

## Commands

### Look up a name by index
```bash
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export name 467
# Output: 467: ite
```

### Look up an expression by index
```bash
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export expr 1608
```

### Trace an expression recursively
```bash
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export trace 1608 5
# Shows nested structure up to depth 5
```

### Show a definition's details
```bash
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export def 467
# Shows type, value, hints for definitions
# Also works for theorems, axioms, inductives, constructors, recursors
```

### Search for names
```bash
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export search Decidable
```

### Find constructors for an inductive type
```bash
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export ctor 458
```

### Find recursor and show its rules
```bash
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export rules 465
```

## Debugging Reduction Failures

### Workflow

1. **Find the failing definition**:
   ```bash
   python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export search BitVec.toInt_eq
   ```

2. **Look up its definition**:
   ```bash
   python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export def <idx>
   ```

3. **Trace the expression structure**:
   ```bash
   python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export trace <expr_idx> 15
   ```

4. **Check recursor rules exist**:
   ```bash
   python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export rules <rec_idx>
   ```

### Understanding ite reduction

`ite` uses this chain: `ite → Decidable.casesOn → Decidable.rec → decidable instance → constructor`

Check each link:
```bash
# Find ite
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export def 467

# Find Decidable.rec rules
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export rules 465

# Find decidable instance for Bool
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export search instDecidableEqBool
python3 .claude/skills/lean-export-analysis/export-analysis.py /tmp/init.export def 556
```

## Export Format Reference

| Entry | Meaning |
|-------|---------|
| `#NS parent name` | String name |
| `#NI parent num` | Numeric name |
| `#EV idx` | Variable (de Bruijn) |
| `#ES level` | Sort |
| `#EC name [levels]` | Constant |
| `#EA fn arg` | Application |
| `#EL #Bx name type body` | Lambda |
| `#EP #Bx name type body` | Pi type |
| `#EZ type idx struct` | Projection |
| `#DEF name type value hints` | Definition |
| `#THM name type value` | Theorem |
| `#IND name ...` | Inductive type |
| `#CTOR name ...` | Constructor |
| `#REC name ...` | Recursor |
| `#RR ctor nfields rhs` | Recursor rule |

Binding info (`#Bx`): `#BD`=default, `#BI`=implicit, `#BC`=instance, `#BS`=strict
