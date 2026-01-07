---
name: export-analysis
description: Analyze Lean 4 export files. Use when debugging trepplein type checking failures, investigating why expressions don't reduce, or exploring the structure of exported definitions.
allowed-tools: Bash, Read, Edit, Write
---

# Export Analysis Tool

This skill provides tools for analyzing Lean 4 export files when debugging the trepplein type checker.

## Self-Improvement Directive

**If you find yourself needing functionality that this tool doesn't provide, or if you believe the script is behaving incorrectly: update the skill yourself.** Don't work around limitations—fix them. Edit `export-analysis.py` to add new commands, improve existing ones, or fix bugs. This tool exists to serve debugging needs; if it's not serving those needs, improve it.

## Tool Location

```
.claude/skills/export-analysis/export-analysis.py
```

## Quick Reference

```bash
# Shorthand alias for the tool
EA="/Users/kim/projects/lean/trepplein/.claude/skills/export-analysis/export-analysis.py"
EXPORT="/tmp/init.export"

python3 $EA $EXPORT <command> [args]
```

## Commands

### Basic Lookups

| Command | Description |
|---------|-------------|
| `name <idx>` | Resolve name index to full path |
| `expr <idx>` | Show expression structure |
| `def <idx>` | Show definition/theorem/axiom details |
| `search <pattern>` | Search for names matching pattern |

### Structure Analysis

| Command | Description |
|---------|-------------|
| `trace <expr> [depth]` | Recursively trace expression structure |
| `app <expr>` | Decompose application into head + args |
| `chain <name> [depth]` | Trace definition unfolding chain |
| `unfold <name>` | Show what a definition unfolds to |

### Inductive Types

| Command | Description |
|---------|-------------|
| `ctor <type>` | Find constructors for an inductive type |
| `rec <type>` | Find recursor for an inductive type |
| `rules <rec>` | Show reduction rules for a recursor |

## Debugging Reduction Failures

### Workflow

1. **Find the failing definition**:
   ```bash
   python3 $EA $EXPORT search BitVec.toInt_eq
   ```

2. **Trace the definition chain** to see what it unfolds to:
   ```bash
   python3 $EA $EXPORT chain <idx>
   ```

3. **Analyze application structure** to see recursor arguments:
   ```bash
   python3 $EA $EXPORT app <expr_idx>
   ```

4. **Check recursor rules exist**:
   ```bash
   python3 $EA $EXPORT rules <rec_idx>
   ```

### Understanding ite reduction

`ite` uses this chain: `ite → Decidable.casesOn → Decidable.rec → decidable instance → constructor`

Example:
```bash
# Trace ite's chain
python3 $EA $EXPORT chain 467

# Check Decidable.rec rules
python3 $EA $EXPORT rules 465
```

### Analyzing Why a Recursor Doesn't Fire

Use `app` to see if the major premise is a constructor:

```bash
# Find a recursor application
python3 $EA $EXPORT app 12345
# Output shows:
#   Head: Const(Nat.rec) - This is a RECURSOR
#     params=0, indices=0, motives=1, minors=2
#     Major premise (arg 3): expr 12340
#       Major head: Nat.zero  <- Should fire rule!
```

If major head is a constructor, the rule should fire. If it's not, the term is stuck.

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
