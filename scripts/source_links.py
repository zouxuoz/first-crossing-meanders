#!/usr/bin/env python3
"""Regenerate blueprint/source-links.json from the blueprint's \\lean{} names
using Lean's declaration ranges, and pin the linked revision.

    python3 scripts/source_links.py [--revision <sha>] [--check]

The default revision is HEAD. `--check` fails if the committed map is stale
or any linked file changed after the pinned revision, so every link still
points at the declaration it names."""
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = ROOT / 'blueprint/src/chapter'
MAP = ROOT / 'blueprint/source-links.json'
ADAPTER = ROOT / 'blueprint/src/plastex/source_links.py'


def blueprint_names():
    names = set()
    for tex in CHAPTERS.glob('*.tex'):
        for group in re.findall(r'\\lean\{([^}]*)\}', tex.read_text()):
            names.update(n.strip() for n in group.split(',') if n.strip())
    return sorted(names)


def locate(names):
    """Ask Lean for the module and first line of every declaration."""
    body = ['import Meanders', 'open Lean', '',
            'def names : List Name := [', ',\n'.join(f'  ``{name}' for name in names), ']', '',
            '#eval show CoreM Unit from do',
            '  let env ← getEnv',
            '  for n in names do',
            '    let some idx := env.getModuleIdxFor? n | throwError m!"no module for {n}"',
            '    let some ranges ← findDeclarationRanges? n | throwError m!"no range for {n}"',
            '    IO.println s!"{n} {env.header.moduleNames[idx.toNat]!} {ranges.range.pos.line}"']
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as f:
        f.write('\n'.join(body) + '\n')
    out = subprocess.run(['lake', 'env', 'lean', f.name], cwd=ROOT, capture_output=True, text=True)
    if out.returncode:
        raise SystemExit(out.stdout + out.stderr)
    locations = {}
    for line in out.stdout.splitlines():
        name, module, number = line.split()
        locations[name] = {'line': int(number), 'path': module.replace('.', '/') + '.lean'}
    return locations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--revision', default=None)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    revision = args.revision or subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    locations = locate(blueprint_names())
    text = json.dumps(locations, indent=2, sort_keys=True) + '\n'
    adapter = re.sub(r"SOURCE_REVISION = '[0-9a-f]{40}'", f"SOURCE_REVISION = '{revision}'",
                     ADAPTER.read_text())
    if args.check:
        assert MAP.read_text() == text, 'blueprint/source-links.json is stale'
        pinned = re.search(r"SOURCE_REVISION = '([0-9a-f]{40})'", ADAPTER.read_text())[1]
        paths = sorted({location['path'] for location in locations.values()})
        changed = subprocess.run(['git', 'diff', '--quiet', pinned, 'HEAD', '--', *paths], cwd=ROOT)
        assert changed.returncode == 0, f'linked Lean files changed since the pinned revision {pinned}'
        print(f'{len(locations)} source links are current and pinned to {pinned}')
    else:
        MAP.write_text(text)
        ADAPTER.write_text(adapter)
        print(f'wrote {len(locations)} source links pinned to {revision}')


if __name__ == '__main__':
    main()
