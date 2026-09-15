#!/usr/bin/env python3
"""Shared declaration audits: resolve names with checkdecls and require the
standard axioms `propext`, `Classical.choice` and `Quot.sound` only."""
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def resolve(names):
    """Fail unless every name is a declaration of the built library."""
    with tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False) as f:
        f.write('\n'.join(names) + '\n')
    subprocess.run(['lake', 'exe', 'checkdecls', f.name], cwd=ROOT, check=True)


def standard_axioms(names):
    """Fail unless every name reports only the standard axioms."""
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as f:
        f.write('import Meanders\nset_option linter.hashCommand false\n')
        f.writelines(f'#print axioms {n}\n' for n in names)
    text = subprocess.check_output(['lake', 'env', 'lean', f.name], cwd=ROOT, text=True)
    for name in names:
        assert f"'{name}'" in text, f'missing axiom report: {name}'
    for group in re.findall(r'depends on axioms: \[([^]]*)\]', text):
        assert set(re.split(r',\s*', group.strip())) <= STANDARD, group
