#!/usr/bin/env python3
"""
Lean 4 Export File Analysis Tool

Usage:
    python export-analysis.py <export_file> <command> [args...]

Commands:
    name <idx>          - Look up a name by index, show full path
    expr <idx>          - Look up an expression by index, show structure
    def <name_idx>      - Show definition for a name
    trace <expr_idx>    - Recursively trace an expression's structure
    deps <name_idx>     - Show what a definition depends on
    rules <name_idx>    - Show reduction rules for a recursor
    search <pattern>    - Search for names matching pattern
    ctor <type_idx>     - Find constructors for an inductive type
    rec <type_idx>      - Find recursor for an inductive type
"""

import sys
import re
from collections import defaultdict

class ExportAnalyzer:
    def __init__(self, filename):
        self.names = {}      # idx -> (kind, data)
        self.exprs = {}      # idx -> (kind, data)
        self.levels = {}     # idx -> (kind, data)
        self.rec_rules = {}  # idx -> (ctor, nfields, rhs)
        self.defs = {}       # name_idx -> (type_idx, value_idx, hints)
        self.thms = {}       # name_idx -> (type_idx, value_idx)
        self.axioms = {}     # name_idx -> type_idx
        self.inds = {}       # name_idx -> data
        self.ctors = {}      # name_idx -> data
        self.recs = {}       # name_idx -> data

        self._parse(filename)

    def _parse(self, filename):
        with open(filename, 'r') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue

                # Indexed entries: "123 #XX ..."
                m = re.match(r'^(\d+) #(\w+) (.*)$', line)
                if m:
                    idx = int(m.group(1))
                    kind = m.group(2)
                    rest = m.group(3)

                    if kind == 'NS':
                        parts = rest.split(' ', 1)
                        parent = int(parts[0])
                        name = parts[1] if len(parts) > 1 else ''
                        self.names[idx] = ('S', parent, name)
                    elif kind == 'NI':
                        parts = rest.split()
                        parent = int(parts[0])
                        num = int(parts[1])
                        self.names[idx] = ('I', parent, num)
                    elif kind.startswith('E'):
                        self.exprs[idx] = (kind, rest)
                    elif kind.startswith('U'):
                        self.levels[idx] = (kind, rest)
                    elif kind == 'RR':
                        parts = rest.split()
                        ctor = int(parts[0])
                        nfields = int(parts[1])
                        rhs = int(parts[2])
                        self.rec_rules[idx] = (ctor, nfields, rhs)
                    continue

                # Declaration entries: "#XX ..."
                m = re.match(r'^#(\w+) (.*)$', line)
                if m:
                    kind = m.group(1)
                    rest = m.group(2)
                    parts = rest.split()

                    if kind == 'DEF':
                        name = int(parts[0])
                        ty = int(parts[1])
                        val = int(parts[2])
                        hints = parts[3] if len(parts) > 3 else ''
                        self.defs[name] = (ty, val, hints)
                    elif kind == 'THM':
                        name = int(parts[0])
                        ty = int(parts[1])
                        val = int(parts[2])
                        self.thms[name] = (ty, val)
                    elif kind == 'AX':
                        name = int(parts[0])
                        ty = int(parts[1])
                        self.axioms[name] = ty
                    elif kind == 'IND':
                        name = int(parts[0])
                        self.inds[name] = parts[1:]
                    elif kind == 'CTOR':
                        name = int(parts[0])
                        self.ctors[name] = parts[1:]
                    elif kind == 'REC':
                        name = int(parts[0])
                        self.recs[name] = parts[1:]

    def resolve_name(self, idx):
        """Resolve a name index to its full path."""
        if idx == 0:
            return ''
        if idx not in self.names:
            return f'<unknown:{idx}>'

        kind, parent, data = self.names[idx]
        parent_name = self.resolve_name(parent)

        if kind == 'S':
            if parent_name:
                return f'{parent_name}.{data}'
            return data
        else:  # 'I'
            if parent_name:
                return f'{parent_name}.{data}'
            return str(data)

    def format_expr(self, idx, depth=0):
        """Format an expression for display."""
        if idx not in self.exprs:
            return f'<expr:{idx}>'

        kind, rest = self.exprs[idx]
        parts = rest.split()
        indent = '  ' * depth

        if kind == 'EV':
            return f'Var({parts[0]})'
        elif kind == 'ES':
            return f'Sort({parts[0]})'
        elif kind == 'EC':
            name_idx = int(parts[0])
            levels = parts[1:] if len(parts) > 1 else []
            name = self.resolve_name(name_idx)
            if levels:
                return f'Const({name}, [{", ".join(levels)}])'
            return f'Const({name})'
        elif kind == 'EA':
            fn = int(parts[0])
            arg = int(parts[1])
            return f'App({self.format_expr(fn)}, {self.format_expr(arg)})'
        elif kind == 'EL':
            # Lambda: #EL #Bx name type body
            binder = parts[0]
            name_idx = int(parts[1])
            ty_idx = int(parts[2])
            body_idx = int(parts[3]) if len(parts) > 3 else int(parts[2])
            binder_str = {'#BD': 'D', '#BI': 'I', '#BC': 'C', '#BS': 'S'}.get(binder, '?')
            return f'Lam[{binder_str}]({self.format_expr(body_idx)})'
        elif kind == 'EP':
            # Pi: similar to Lambda
            binder = parts[0]
            return f'Pi[{binder}](...)'
        elif kind == 'EZ':
            return f'Proj({parts[0]}, {parts[1]}, {parts[2]})'
        elif kind == 'ELN':
            return f'NatLit({parts[0]})'
        elif kind == 'ELS':
            return f'StrLit(...)'
        else:
            return f'{kind}({rest})'

    def trace_expr(self, idx, depth=0, max_depth=10):
        """Recursively trace an expression's structure."""
        if depth > max_depth:
            return '  ' * depth + '...(max depth)\n'

        if idx not in self.exprs:
            return '  ' * depth + f'<expr:{idx}>\n'

        kind, rest = self.exprs[idx]
        parts = rest.split()
        indent = '  ' * depth
        result = ''

        if kind == 'EV':
            result = f'{indent}Var({parts[0]})\n'
        elif kind == 'ES':
            result = f'{indent}Sort(level:{parts[0]})\n'
        elif kind == 'EC':
            name_idx = int(parts[0])
            name = self.resolve_name(name_idx)
            levels = parts[1:] if len(parts) > 1 else []
            result = f'{indent}Const({name})\n'
        elif kind == 'EA':
            fn = int(parts[0])
            arg = int(parts[1])
            result = f'{indent}App\n'
            result += self.trace_expr(fn, depth + 1, max_depth)
            result += self.trace_expr(arg, depth + 1, max_depth)
        elif kind == 'EL':
            binder = parts[0]
            binder_str = {'#BD': 'default', '#BI': 'implicit', '#BC': 'inst', '#BS': 'strict'}.get(binder, binder)
            if len(parts) >= 4:
                name_idx = int(parts[1])
                ty_idx = int(parts[2])
                body_idx = int(parts[3])
            else:
                name_idx = int(parts[1])
                ty_idx = int(parts[2])
                body_idx = ty_idx  # fallback
            result = f'{indent}Lam[{binder_str}] (type:{ty_idx})\n'
            result += self.trace_expr(body_idx, depth + 1, max_depth)
        elif kind == 'EP':
            binder = parts[0]
            binder_str = {'#BD': 'default', '#BI': 'implicit', '#BC': 'inst', '#BS': 'strict'}.get(binder, binder)
            if len(parts) >= 4:
                body_idx = int(parts[3])
            else:
                body_idx = int(parts[2])
            result = f'{indent}Pi[{binder_str}]\n'
            result += self.trace_expr(body_idx, depth + 1, max_depth)
        else:
            result = f'{indent}{kind}({rest})\n'

        return result

    def show_def(self, name_idx):
        """Show a definition's details."""
        name = self.resolve_name(name_idx)

        if name_idx in self.defs:
            ty, val, hints = self.defs[name_idx]
            print(f"Definition: {name} (idx: {name_idx})")
            print(f"  Type expr: {ty}")
            print(f"  Value expr: {val}")
            print(f"  Hints: {hints}")
            return

        if name_idx in self.thms:
            ty, val = self.thms[name_idx]
            print(f"Theorem: {name} (idx: {name_idx})")
            print(f"  Type expr: {ty}")
            print(f"  Proof expr: {val}")
            return

        if name_idx in self.axioms:
            ty = self.axioms[name_idx]
            print(f"Axiom: {name} (idx: {name_idx})")
            print(f"  Type expr: {ty}")
            return

        if name_idx in self.inds:
            data = self.inds[name_idx]
            print(f"Inductive: {name} (idx: {name_idx})")
            print(f"  Data: {' '.join(data)}")
            return

        if name_idx in self.ctors:
            data = self.ctors[name_idx]
            print(f"Constructor: {name} (idx: {name_idx})")
            print(f"  Data: {' '.join(data)}")
            return

        if name_idx in self.recs:
            data = self.recs[name_idx]
            print(f"Recursor: {name} (idx: {name_idx})")
            print(f"  Data: {' '.join(data)}")
            return

        print(f"Name: {name} (idx: {name_idx}) - no definition found")

    def find_by_name(self, pattern):
        """Search for names matching a pattern."""
        results = []
        for idx in self.names:
            name = self.resolve_name(idx)
            if pattern.lower() in name.lower():
                results.append((idx, name))
        return results

    def find_constructors(self, type_idx):
        """Find constructors for an inductive type."""
        results = []
        type_name = self.resolve_name(type_idx)
        for name_idx, data in self.ctors.items():
            if len(data) >= 2 and int(data[1]) == type_idx:
                results.append((name_idx, self.resolve_name(name_idx)))
        return results

    def find_recursor(self, type_idx):
        """Find recursor for an inductive type."""
        type_name = self.resolve_name(type_idx)
        for name_idx, data in self.recs.items():
            # Check if this recursor is for our type
            if len(data) >= 3 and int(data[2]) == type_idx:
                return (name_idx, self.resolve_name(name_idx), data)
        return None

    def show_rec_rules(self, rec_name_idx):
        """Show reduction rules for a recursor."""
        if rec_name_idx not in self.recs:
            print(f"Not a recursor: {rec_name_idx}")
            return

        data = self.recs[rec_name_idx]
        name = self.resolve_name(rec_name_idx)
        print(f"Recursor: {name}")
        print(f"  Raw data: {' '.join(data)}")

        # Parse recursor data to find rule indices
        # Format: type numUniv inductName numParams numIndices numMotives numMinors numRules rule1 rule2 ... isK univs
        if len(data) >= 8:
            num_rules = int(data[6])
            rule_indices = [int(data[7 + i]) for i in range(num_rules)]

            print(f"  Num rules: {num_rules}")
            for rule_idx in rule_indices:
                if rule_idx in self.rec_rules:
                    ctor, nfields, rhs = self.rec_rules[rule_idx]
                    ctor_name = self.resolve_name(ctor)
                    print(f"  Rule {rule_idx}: ctor={ctor_name}, fields={nfields}, rhs_expr={rhs}")


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)

    filename = sys.argv[1]
    command = sys.argv[2]
    args = sys.argv[3:]

    analyzer = ExportAnalyzer(filename)

    if command == 'name':
        idx = int(args[0])
        print(f"{idx}: {analyzer.resolve_name(idx)}")

    elif command == 'expr':
        idx = int(args[0])
        print(analyzer.format_expr(idx))

    elif command == 'trace':
        idx = int(args[0])
        max_depth = int(args[1]) if len(args) > 1 else 10
        print(analyzer.trace_expr(idx, max_depth=max_depth))

    elif command == 'def':
        idx = int(args[0])
        analyzer.show_def(idx)

    elif command == 'search':
        pattern = args[0]
        results = analyzer.find_by_name(pattern)
        for idx, name in sorted(results, key=lambda x: x[1]):
            print(f"{idx}: {name}")

    elif command == 'ctor':
        idx = int(args[0])
        results = analyzer.find_constructors(idx)
        for cidx, name in results:
            print(f"{cidx}: {name}")

    elif command == 'rec':
        idx = int(args[0])
        result = analyzer.find_recursor(idx)
        if result:
            ridx, name, data = result
            print(f"{ridx}: {name}")
            print(f"  Data: {' '.join(data)}")
        else:
            print("No recursor found")

    elif command == 'rules':
        idx = int(args[0])
        analyzer.show_rec_rules(idx)

    else:
        print(f"Unknown command: {command}")
        print(__doc__)
        sys.exit(1)


if __name__ == '__main__':
    main()
