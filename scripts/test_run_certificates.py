#!/usr/bin/env python3
"""Independent SHA/Merkle reference and end-to-end version-one contract tests."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def merkle(leaves):
    if not leaves:
        return hashlib.sha256(b'').digest()
    if len(leaves) == 1:
        return hashlib.sha256(b'\0' + leaves[0]).digest()
    k = 1 << ((len(leaves) - 1).bit_length() - 1)
    return hashlib.sha256(b'\1' + merkle(leaves[:k]) + merkle(leaves[k:])).digest()


def commitment(m):
    header = '\n'.join(map(str, ['meanders-run-v1', m['problem'], m['algorithm'],
                                    m['n'], m['count'], m['representation'], len(m['layers'])])) + '\n'
    if m.get('firstCrossing') is not None:
        fc = m['firstCrossing']
        header += '\n'.join(map(str, ['first-crossing', fc['nativeOrder'], fc['threshold'],
                                      fc['closed'], fc['openEven'], len(fc['sectors'])])) + '\n'
        for summary in fc['sectors']:
            sector = summary['sector']
            identity = ['sector', sector['kind']]
            if sector['kind'] == 'high':
                identity += [sector['cut'], sector['upper'], sector['lower']]
            header += '\n'.join(map(str, identity + [summary['ordinary'], summary['lowerReturns'],
                                                    summary['bonusContribution']])) + '\n'
    leaves = [header.encode()]
    for t, layer in enumerate(m['layers']):
        symmetric = layer['symmetric'] if layer['symmetric'] is not None else '-'
        text = '\n'.join(map(str, ['layer', t, layer['rows'], layer['bytes'],
                                  layer['ordinary'], symmetric, layer['sha256']])) + '\n'
        if 'lowerReturns' in layer:
            text += f"lower-returns\n{layer['lowerReturns']}\n"
        leaves.append(text.encode())
    return merkle(leaves).hex()


def descriptor(data, *, lower=False):
    rows = [line.split(' ') for line in data.decode().splitlines()]
    out = dict(rows=len(rows), bytes=len(data), ordinary=sum(int(r[1]) for r in rows),
               symmetric=None, sha256=digest(data))
    if lower:
        out['lowerReturns'] = sum(int(r[2]) for r in rows)
    return out


def main():
    producer = ROOT / 'rust/target/release/meanders'
    verifier = ROOT / '.lake/build/bin/verify'
    with tempfile.TemporaryDirectory(prefix='meanders-run-') as tmp:
        work = Path(tmp)
        checks = 0

        def verify(path, accept=True, reason=None):
            nonlocal checks
            result = subprocess.run([verifier, path], capture_output=True, text=True)
            marker = 'ACCEPT: ' if accept else 'REJECT: '
            assert result.returncode == (0 if accept else 1), (path, result)
            assert not result.stderr and result.stdout.startswith(marker), result
            assert result.stdout.count('ACCEPT: ') + result.stdout.count('REJECT: ') == 1, result
            if reason:
                assert reason in result.stdout, result.stdout
            checks += 1

        def emit(problem, algorithm, n, profile, name):
            path = work / f'{name}.json'
            command = [producer, 'count', '--problem', problem, '--algorithm', algorithm,
                       '--n', str(n), '--out', path]
            if profile:
                command += ['--cert', profile]
            subprocess.run(command, check=True, capture_output=True)
            m = json.loads(path.read_text())
            assert m['kind'] == 'run' and m['version'] == 1
            assert commitment(m) == m['root'], m
            for l in m['layers']:
                if 'file' in l:
                    data = (work / l['file']).read_bytes()
                    assert {k: v for k, v in l.items() if k != 'file'} == descriptor(data)
            verify(path)
            return path, m

        def modified(m, name, update=None, accept=False, reason=None, resign=True):
            m = copy.deepcopy(m)
            if update:
                update(m)
            if resign:
                m['root'] = commitment(m)
            path = work / f'{name}.json'
            path.write_text(json.dumps(m))
            verify(path, accept, reason)
            return m

        # Each curated fixture still reaches its intended rejection stage.
        for fixture, reason in [
            ('reject/unknown-certificate-kind.json', 'unrecognized certificate kind: tree'),
            ('run/reject/incompatible-representation.json', 'incompatible run representation'),
            ('run/reject/claim-unknown-problem.json', 'unknown problem tag: unknown'),
            ('run/reject/claim-unknown-algorithm.json', 'unknown algorithm tag: unknown'),
            ('run/reject/unsupported-version.json', 'unsupported run version'),
        ]:
            verify(ROOT / 'fixtures/certificates' / fixture, False, reason)

        # Unsigned tampering: a changed count with the old root fails the root check.
        _, m = emit('closed', 'brute_force', 4, 'compact', 'unsigned')
        modified(m, 'unsigned-count', lambda m: m.update(count=m['count'] + 1), resign=False,
                 reason='root mismatch')
        for problem, algorithm in [('closed', 'brute_force'), ('open', 'brute_force')]:
            _, m = emit(problem, algorithm, 3, 'compact', f'count-{problem}-{algorithm}')
            assert m['representation'] == 'count' and not m['layers']
            modified(m, f'false-{problem}', lambda m: m.update(count=m['count'] + 1))
        # An unknown algorithm must reject before creating any output.
        unknown_path = work / 'unknown-algorithm.json'
        result = subprocess.run([producer, 'count', '--problem', 'closed', '--algorithm',
                                 'unknown', '--n', '6', '--out', str(unknown_path)],
                                capture_output=True, text=True)
        assert result.returncode != 0 and 'unknown algorithm' in result.stderr, result
        assert not unknown_path.exists()
        for args in [ ['--algorithm', 'brute_force', '--problem', 'closed', '--n', '2', '--cert', 'full'] ]:
            result = subprocess.run([producer, 'count', *args], capture_output=True, text=True)
            assert result.returncode != 0, args
        print(f'    ok: {checks} versioned run verification cases, independent commitments, retention and CLI contracts')


if __name__ == '__main__':
    main()
