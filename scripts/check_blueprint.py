#!/usr/bin/env python3
"""After `leanblueprint pdf` and `leanblueprint web`: the rendered TikZ images,
dependency graph and Lean source links are present, and every `\\lean{}`
declaration uses only standard axioms."""
import json
import re
from pathlib import Path

from audit import ROOT, resolve, standard_axioms

FIGURES = 4


def main():
    web = ROOT / 'blueprint/web'
    html = (web / 'index.html').read_text()
    figures = [n for n in re.findall(r'<img[^>]+src="([^"]+)"', html) if n.startswith('images/')]
    assert len(figures) == FIGURES, f'expected {FIGURES} TikZ images, found {figures}'
    assert all((web / n).is_file() and (web / n).stat().st_size > 1000 for n in figures)
    graph = web / 'dep_graph_document.html'
    assert graph.is_file() and 'thm:main' in graph.read_text()

    revision = re.search(r"SOURCE_REVISION = '([0-9a-f]{40})'",
                         (ROOT / 'blueprint/src/plastex/source_links.py').read_text())[1]
    assert f'/blob/{revision}/Meanders/' in html, 'source links are not pinned to the recorded revision'
    assert 'mathlib4_docs/find/#doc/Meanders.' not in html
    locations = json.loads((ROOT / 'blueprint/source-links.json').read_text())
    for name, location in locations.items():
        lines = (ROOT / location['path']).read_text().splitlines()
        assert 1 <= location['line'] <= len(lines), name

    names = sorted(set((ROOT / 'blueprint/lean_decls').read_text().split()))
    assert set(names) == set(locations), 'source-links.json and lean_decls name different declarations'
    resolve(names)
    standard_axioms(names)
    print(f'{FIGURES} images, dependency graph, {len(locations)} source links and '
          f'{len(names)} blueprint declarations verified')


if __name__ == '__main__':
    main()
