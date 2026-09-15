#!/usr/bin/env python3
"""First-Crossing CLI -> retained/regenerated Lean verification contract tests.

Run after building the registered verifier and release Rust CLI. Commitments are
recomputed independently here; only the verifier checks the recurrence.
"""

import argparse
import copy
import json
from pathlib import Path
import subprocess
import tempfile

from test_run_certificates import ROOT, commitment, descriptor


def scale_weights(manifest, directory, prefix):
    """Coherently forge all weights and commitments; the fixed seed must reject it."""
    for index, layer in enumerate(manifest['layers']):
        rows = []
        for row in (directory / layer['file']).read_text().splitlines():
            key, ordinary, lower = row.split(' ')
            rows.append(f'{key} {2 * int(ordinary)} {2 * int(lower)}\n')
        payload = ''.join(rows).encode()
        filename = f'{prefix}-layer-{index}.txt'
        (directory / filename).write_bytes(payload)
        layer.update(descriptor(payload, lower=True), file=filename)
    for field in ['closed', 'openEven']:
        manifest['firstCrossing'][field] *= 2
    for sector in manifest['firstCrossing']['sectors']:
        for field in ['ordinary', 'lowerReturns', 'bonusContribution']:
            sector[field] *= 2
    manifest['count'] *= 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--producer', type=Path, default=ROOT / 'rust/target/release/meanders')
    parser.add_argument('--verifier', type=Path, default=ROOT / '.lake/build/bin/verify')
    parser.add_argument('--max-order', type=int, default=3)
    args = parser.parse_args()
    if not 1 <= args.max_order <= 8:
        parser.error('--max-order must be between 1 and 8')
    checks = 0
    with tempfile.TemporaryDirectory(prefix='meanders-first-crossing-run-') as tmp:
        work = Path(tmp)

        def verify(path, accept=True, reason=None, timeout=None):
            nonlocal checks
            result = subprocess.run([args.verifier, path], capture_output=True, text=True, timeout=timeout)
            marker = 'ACCEPT: ' if accept else 'REJECT: '
            assert result.returncode == (0 if accept else 1), (path.name, result)
            assert not result.stderr and result.stdout.startswith(marker), (path.name, result)
            assert result.stdout.count('ACCEPT: ') + result.stdout.count('REJECT: ') == 1, result
            if reason is not None:
                assert reason in result.stdout, (path.name, result.stdout)
            checks += 1

        def emit(problem, n, profile, name, algorithm='first_crossing'):
            path = work / f'{name}.json'
            subprocess.run([args.producer, 'count', '--algorithm', algorithm,
                            '--problem', problem, '--n', str(n), '--cert', profile,
                            '--out', path], check=True, capture_output=True)
            manifest = json.loads(path.read_text())
            assert manifest['representation'] == 'first-crossing-lower-jet'
            assert commitment(manifest) == manifest['root']
            for layer in manifest['layers']:
                if 'file' in layer:
                    data = (work / layer['file']).read_bytes()
                    assert {k: v for k, v in layer.items() if k != 'file'} == descriptor(data, lower=True)
            verify(path)
            return manifest

        def modified(base, name, change, accept=False, reroot=True, reason=None, timeout=None):
            manifest = copy.deepcopy(base)
            change(manifest)
            if reroot:
                manifest['root'] = commitment(manifest)
            path = work / f'{name}.json'
            path.write_text(json.dumps(manifest))
            verify(path, accept, reason, timeout)
            return manifest

        cases = [('closed', 0), ('open', 0)]
        for rank in range(1, args.max_order + 1):
            cases += [('closed', rank), ('open', 2 * rank - 1), ('open', 2 * rank)]
        for problem, n in cases:
            name = f'{problem}-{n}'
            full = emit(problem, n, 'full', name)
            compact = emit(problem, n, 'compact', name + '-compact')
            assert full['root'] == compact['root']
            assert not list(work.glob(name + '-compact-layer-*'))
            fc = compact['firstCrossing']
            if n == 0:
                assert (fc['nativeOrder'], fc['threshold'], fc['closed'], fc['openEven']) == (0, 0, 0, 1)
                assert not fc['sectors'] and not compact['layers']
            modified(full, name + '-retained-compact', lambda m: m.update(profile='compact'), accept=True)
            if full['layers']:
                modified(full, name + '-mixed', lambda m: (m.update(profile='compact'),
                         m['layers'][1].pop('file')), accept=True)
            # Compatible count evidence keeps the same registered public evaluator.
            modified(compact, name + '-count', lambda m: (m.update(representation='count', layers=[]),
                     m.pop('firstCrossing')), accept=True)
            optimized = emit(problem, n, 'compact', name + '-optimized', 'first_crossing_optimized')
            canonical = copy.deepcopy(compact)
            canonical['algorithm'] = 'first_crossing_optimized'
            canonical['root'] = commitment(canonical)
            assert optimized == canonical
            modified(optimized, name + '-optimized-count', lambda m:
                     (m.update(representation='count', layers=[]), m.pop('firstCrossing')),
                     accept=True)


        for path in sorted((ROOT / 'fixtures/certificates/first-crossing').glob('*.json')):
            assert commitment(json.loads(path.read_text())) == json.loads(path.read_text())['root']
            verify(path)

        emit('open', 4, 'full', 'optimized-retained', 'first_crossing_optimized')
        full = emit('open', 2, 'full', 'high-bonus')
        assert any(s['bonusContribution'] > 0 for s in full['firstCrossing']['sectors'])
        compact = emit('closed', 3, 'compact', 'tamper-base')
        changes = {
            'missing-metadata': lambda m: m.pop('firstCrossing'),
            'wrong-native-order': lambda m: m['firstCrossing'].update(nativeOrder=4),
            'wrong-threshold': lambda m: m['firstCrossing'].update(threshold=0),
            'missing-sector': lambda m: m['firstCrossing']['sectors'].pop(),
            'reordered-sectors': lambda m: m['firstCrossing']['sectors'].reverse(),
            'duplicate-sector': lambda m: m['firstCrossing']['sectors'].__setitem__(1,
                copy.deepcopy(m['firstCrossing']['sectors'][0])),
            'wrong-ordinary': lambda m: m['firstCrossing']['sectors'][0].update(ordinary=999),
            'wrong-lower-moment': lambda m: m['firstCrossing']['sectors'][0].update(lowerReturns=999),
            'wrong-bonus': lambda m: m['firstCrossing']['sectors'][0].update(bonusContribution=1),
            'wrong-closed-total': lambda m: m['firstCrossing'].update(closed=999),
            'wrong-even-total': lambda m: m['firstCrossing'].update(openEven=999),
            'wrong-public-count': lambda m: m.update(count=999),
            'missing-lower-channel': lambda m: m['layers'][0].pop('lowerReturns'),
            'symmetric-channel': lambda m: m['layers'][0].update(symmetric=0),
            'missing-layer': lambda m: m['layers'].pop(),
            'extra-layer': lambda m: m['layers'].append(copy.deepcopy(m['layers'][-1])),
            'wrong-digest': lambda m: m['layers'][0].update(sha256='f' * 64),
            'wrong-bytes': lambda m: m['layers'][0].update(bytes=123),
            'wrong-rows': lambda m: m['layers'][0].update(rows=123),
            'wrong-representation': lambda m: m.update(representation='unknown'),
        }
        for name, change in changes.items():
            modified(compact, name, change)
        # These tiny manifests must reject before quadratic source enumeration.
        huge = 10**9
        modified(compact, 'huge-order-empty-sectors', lambda m:
                 (m.update(n=huge, layers=[]), m['firstCrossing'].update(
                     nativeOrder=huge, threshold=1, sectors=[])),
                 reason='positive-order First-Crossing evidence must include sectors', timeout=5)
        modified(compact, 'huge-order-missing-layers', lambda m:
                 (m.update(n=huge, layers=[]), m['firstCrossing'].update(
                     nativeOrder=huge, threshold=1)),
                 reason='wrong number of First-Crossing sector layers', timeout=5)
        modified(compact, 'huge-native-order-mismatch', lambda m:
                 m['firstCrossing'].update(nativeOrder=huge, threshold=1),
                 reason='First-Crossing closed claim mismatch', timeout=5)
        modified(compact, 'bad-root', lambda m: m.update(root='0' * 64), reroot=False)
        modified(full, 'missing-file', lambda m: m['layers'][0].update(file='absent.txt'))
        modified(full, 'missing-full-location', lambda m: m['layers'][0].pop('file'))
        modified(full, 'compact-missing-file', lambda m: (m.update(profile='compact'),
                 m['layers'][0].update(file='absent.txt')))
        # The whole HIGH sector is omitted coherently, including its layers.
        def omit_sector(m):
            steps = 2 * m['firstCrossing']['nativeOrder'] + 1
            m['firstCrossing']['sectors'].pop(1)
            del m['layers'][steps:2 * steps]
        modified(compact, 'coherent-sector-omission', omit_sector)

        # Preserve metadata and a coherent descriptor/root while forging a native transition.
        full = emit('closed', 3, 'full', 'forged-base')
        # Use a later sector so the diagnostic must distinguish local/global indices.
        index = next(i for i, layer in enumerate(full['layers'])
                     if i >= 7 and i % 7 not in (0, 6) and layer['rows'] > 0)
        original = (work / full['layers'][index]['file']).read_text()
        first, *rest = original.splitlines()
        key, c, e = first.split(' ')
        payloads = {
            'false-weight': f'{key} {int(c) + 1} {e}\n' + ''.join(r + '\n' for r in rest),
            'false-increment': f'{key} {c} {int(e) + 1}\n' + ''.join(r + '\n' for r in rest),
            'noncanonical-weight': f'{key} 0{c} {e}\n' + ''.join(r + '\n' for r in rest),
            'malformed-counters': f'999,0,0,0| {c} {e}\n',
            'malformed-pairing': f'0,0,0,0|0 {c} {e}\n',
            'omitted-transition': '',
            'duplicate-row': original + first + '\n',
        }
        for name, text in payloads.items():
            filename = name + '.txt'
            data = text.encode()
            (work / filename).write_bytes(data)
            modified(full, name, lambda m, data=data, filename=filename: m['layers'].__setitem__(index,
                     dict(descriptor(data, lower=True), file=filename)))
        def early_failure(m):
            data = payloads['false-weight'].encode()
            m['layers'][index] = dict(descriptor(data, lower=True), file='false-weight.txt')
            for layer in m['layers'][index + 1:]:
                layer['file'] = 'absent-after-bad-transition.txt'
        modified(full, 'early-transition-failure', early_failure,
                 reason=f'starting at global layer {(index // 7) * 7}: '
                        f'layer {index % 7} is not the successor of layer {index % 7 - 1}')
        modified(full, 'scaled-weights', lambda m: scale_weights(m, work, 'scaled'),
                 reason='layer 0 is not the initial state')
        # Unsupported problems/tags must fail before creating an output manifest.
        for algorithm, problem in [('first_crossing', 'unknown'), ('first_crossing_optimized', 'unknown'),
                                   ('unknown', 'closed')]:
            path = work / f'unsupported-{algorithm}-{problem}.json'
            result = subprocess.run([args.producer, 'count', '--algorithm', algorithm,
                                     '--problem', problem, '--n', '1', '--out', path], capture_output=True)
            assert result.returncode != 0 and not path.exists()
            reason = b'unknown problem' if problem == 'unknown' else b'unknown algorithm'
            assert reason in result.stderr, result
        print(f'    ok: {checks} First-Crossing verification cases, independent commitments, sectors, '
              'retained/regenerated layers, count compatibility and malformed inputs')


if __name__ == '__main__':
    main()
