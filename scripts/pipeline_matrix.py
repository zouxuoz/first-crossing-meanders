#!/usr/bin/env python3
"""Produce every evaluator's certificates at small orders and verify each in Lean.

One native run per (evaluator, index, profile, workers) through
`meanders count --problem all`, so the closed/open families are covered
for closed, even open and odd open from one evaluation. Every manifest
must recompute its own root, match its layer files, and be accepted by
the Lean verifier with the expected report line. Across evaluators, every
public value must agree with every other evaluator that produced it and
with fixtures/oeis, and evaluators sharing a representation must emit
identical layer descriptors. Run by scripts/pipeline.sh after the builds.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_run_certificates import commitment, descriptor  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
PRODUCER = Path(os.environ.get('MEANDERS_BIN', ROOT / 'rust/target/release/meanders'))
VERIFIER = Path(os.environ.get('VERIFY_BIN', ROOT / '.lake/build/bin/verify'))

# evaluator -> (compact through native index, full through native index, worker counts)
MATRIX = {
    'first_crossing': (7, 6, [0]),
    'first_crossing_optimized': (7, 6, [0, 3]),
}
# brute_force has no native run; it names each problem.
BRUTE_FORCE = {'closed': 8, 'open': 8}
SAME_LAYERS = [('first_crossing', 'first_crossing_optimized')]


def golden():
    values = {}
    for problem in ('closed', 'open'):
        for line in (ROOT / f'fixtures/oeis/{problem}.txt').read_text().splitlines():
            if line[:1].isdigit():
                n, count = line.split()[:2]
                values[(problem, int(n))] = int(count)
    return values


class Matrix:
    def __init__(self, work):
        self.work = work
        self.golden = golden()
        self.counts = {}      # (problem, n) -> {evaluator: count}
        self.layers = {}      # (evaluator, problem, n) -> layers without files, plus extension
        self.runs = self.manifests = self.checks = 0
        self.failures = []

    def fail(self, message):
        self.failures.append(message)
        print(f'    FAIL: {message}', file=sys.stderr)

    def check(self, condition, message):
        self.checks += 1
        if not condition:
            self.fail(message)

    def verify(self, path, problem, n, count):
        result = subprocess.run([VERIFIER, path], capture_output=True, text=True)
        expected = f'ACCEPT: {problem} meander number {n} = {count}'
        lines = result.stdout.splitlines()
        ok = (result.returncode == 0 and not result.stderr and len(lines) == 1
              and lines[0].startswith(expected + ' ('))
        self.check(ok, f'{path.name}: exit {result.returncode}, {result.stdout!r} {result.stderr!r}')

    def manifest(self, path, evaluator, profile, directory):
        m = json.loads(path.read_text())
        problem, n, count = m['problem'], m['n'], m['count']
        label = f'{evaluator} {problem} {n} {profile}'
        self.check(m['kind'] == 'run' and m['version'] == 1 and m['profile'] == profile,
                   f'{label}: metadata')
        self.check(commitment(m) == m['root'], f'{label}: root')
        for layer in m['layers']:
            if profile == 'full':
                data = (directory / layer['file']).read_bytes()
                expected = descriptor(data,
                                      lower=evaluator.startswith('first_crossing'))
                self.check({k: v for k, v in layer.items() if k != 'file'} == expected,
                           f'{label}: layer descriptor')
            else:
                self.check('file' not in layer, f'{label}: compact wrote a payload reference')
        self.verify(path, problem, n, count)
        self.manifests += 1
        self.counts.setdefault((problem, n), {})[evaluator] = count
        stripped = [{k: v for k, v in l.items() if k != 'file'} for l in m['layers']]
        key = (evaluator, problem, n)
        previous = self.layers.setdefault(key, (m['root'], stripped, m.get('firstCrossing')))
        self.check(previous[0] == m['root'], f'{label}: full and compact roots differ')

    def native(self, evaluator, n, profile, threads):
        directory = self.work / f'{evaluator}-{n}-{profile}-t{threads}'
        command = [PRODUCER, 'count', '--problem', 'all', '--algorithm', evaluator, '--n', str(n),
                   '--cert', profile, '--out', directory]
        if threads:
            command += ['--threads', str(threads)]
        result = subprocess.run(command, capture_output=True, text=True)
        self.runs += 1
        if result.returncode or result.stderr:
            self.fail(f'{evaluator} n={n} {profile}: producer exit {result.returncode} {result.stderr!r}')
            return
        paths = [Path(line.split(' ', 3)[3]) for line in result.stdout.splitlines()]
        self.check(len(paths) == len(list(directory.glob('*.json'))),
                   f'{evaluator} n={n}: printed lines differ from manifests written')
        for path in paths:
            self.manifest(path, evaluator, profile, directory)

    def brute_force(self, problem, n):
        path = self.work / f'brute_force-{problem}-{n}.json'
        subprocess.run([PRODUCER, 'count', '--problem', problem, '--algorithm', 'brute_force',
                        '--n', str(n), '--cert', 'compact', '--out', path], check=True)
        self.runs += 1
        self.manifest(path, 'brute_force', 'compact', self.work)

    def cross_check(self):
        for (problem, n), by_evaluator in sorted(self.counts.items()):
            values = set(by_evaluator.values())
            self.check(len(values) == 1, f'{problem} {n}: evaluators disagree {by_evaluator}')
            if (problem, n) in self.golden:
                self.check(values == {self.golden[(problem, n)]},
                           f'{problem} {n}: {values} differs from fixtures/oeis')
        for a, b in SAME_LAYERS:
            for (evaluator, problem, n), (_, layers, extension) in sorted(self.layers.items()):
                if evaluator != a or (b, problem, n) not in self.layers:
                    continue
                _, other, other_extension = self.layers[(b, problem, n)]
                self.check(layers == other and extension == other_extension,
                           f'{a} and {b} differ on {problem} {n}')


def main():
    with tempfile.TemporaryDirectory(prefix='meanders-matrix-') as tmp:
        matrix = Matrix(Path(tmp))
        for evaluator, (compact_max, full_max, workers) in MATRIX.items():
            for n in range(compact_max + 1):
                for threads in workers:
                    matrix.native(evaluator, n, 'compact', threads)
                    if full_max is not None and n <= full_max:
                        matrix.native(evaluator, n, 'full', threads)
        for problem, limit in BRUTE_FORCE.items():
            for n in range(limit + 1):
                matrix.brute_force(problem, n)
        matrix.cross_check()
        summary = (f'{matrix.runs} runs, {matrix.manifests} manifests verified, '
                   f'{len(matrix.counts)} public values cross-checked, {matrix.checks} checks')
        if matrix.failures:
            sys.exit(f'    FAIL: {len(matrix.failures)} failures in {summary}')
        print(f'    ok: {summary}')


if __name__ == '__main__':
    main()
