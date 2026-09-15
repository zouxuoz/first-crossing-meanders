#!/usr/bin/env python3
"""Record a native First-Crossing run, measurements and compiled Lean verdicts.

Build first: cargo build --release --manifest-path rust/Cargo.toml; lake build verify
Example: scripts/evaluate.py --host m2max --evaluator first_crossing_optimized --n 3

Always uses --problem all at native order n, producing Closed(n), Open(2n),
and Open(2n-1) where supported. Only the two First-Crossing evaluators are accepted.
Each invocation creates evaluations/<evaluator>/n-<N>/<UTC timestamp>/
with certificates and meta.json. --out changes the evaluations root.

--cert is passed to the CLI unchanged, including its auto policy. --verify auto
runs the compiled Lean checker through native order 10; always/never override it.
ACCEPT is not numerical kernel replay.
Measurements exclude builds and record wall time, child peak RSS and exit status;
command output is limited to the first 4 KiB by measure.py.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

import measure

ROOT = Path(__file__).resolve().parents[1]
VERIFY_MAX_ORDER = 10
EVALUATORS = ('first_crossing', 'first_crossing_optimized')
MEANDERS = ROOT / 'rust/target/release/meanders'
VERIFY = ROOT / '.lake/build/bin/verify'
EVALUATIONS = ROOT / 'evaluations'
# `optimized::MAX_WORKERS`: one worker per key-hash bucket; larger requests use this many.
MAX_WORKERS = 256


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def step(name, command, host):
    command = [str(c) for c in command]
    report = measure.measure(command, host, repeat=1)
    return {'name': name, 'command': command, **report['samples'][0]}, report


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--host', required=True, help='short machine label, e.g. m2max')
    parser.add_argument('--evaluator', required=True, choices=EVALUATORS)
    parser.add_argument('--n', type=int, required=True, help='native First-Crossing order')
    parser.add_argument('--threads', type=int, default=0,
                        help='optimized workers; 0 keeps the CLI default (one worker)')
    parser.add_argument('--cert', choices=['auto', 'full', 'compact', 'count'], default='auto')
    parser.add_argument('--verify', choices=['auto', 'always', 'never'], default='auto')
    parser.add_argument('--out', type=Path, default=EVALUATIONS, help='evaluations root')
    args = parser.parse_args()
    if not measure.HOST_LABEL.fullmatch(args.host):
        parser.error('--host must be lowercase letters, digits and hyphens')
    if platform.system() not in ('Darwin', 'Linux'):
        parser.error('peak RSS units are supported on macOS and Linux only')
    if args.n < 0 or args.threads < 0:
        parser.error('--n and --threads must be nonnegative')
    if args.threads and args.evaluator != 'first_crossing_optimized':
        parser.error('--threads applies to first_crossing_optimized only')
    if not MEANDERS.is_file():
        parser.error(f'{MEANDERS} is missing; build the release CLI first')
    verify = args.verify == 'always' or (args.verify == 'auto' and args.n <= VERIFY_MAX_ORDER)
    if verify and not VERIFY.is_file():
        parser.error(f'{VERIFY} is missing; run `lake build verify` or pass --verify never')

    timestamp = datetime.datetime.now(datetime.timezone.utc)
    directory = (args.out.resolve() / args.evaluator.replace('_', '-') /
                 f'n-{args.n}' / timestamp.strftime('%Y%m%dT%H%M%S%fZ'))
    # Resolve the caller's output path first; measure git state in this checkout.
    os.chdir(ROOT)
    directory.mkdir(parents=True)
    print(directory, flush=True)
    command = [MEANDERS, 'count', '--problem', 'all', '--algorithm', args.evaluator,
               '--n', str(args.n), '--cert', args.cert, '--out', directory]
    if args.threads:
        command += ['--threads', str(args.threads)]
    production, report = step('produce', command, args.host)
    values = []
    verifications = []
    error = None
    if production['exit_code']:
        error = f'production failed with exit {production["exit_code"]}'
    else:
        try:
            for path in sorted(directory.glob('*.json')):
                manifest = json.loads(path.read_text())
                values.append({
                    'problem': manifest['problem'], 'n': manifest['n'],
                    'count': str(manifest['count']), 'certificate': path.name,
                    'profile': manifest['profile'], 'root': manifest['root'],
                    'representation': manifest['representation'], 'verified': None,
                })
            if not values:
                raise ValueError('producer emitted no manifests')
        except (OSError, ValueError, KeyError) as exc:
            error = f'reading certificates: {exc}'

    if verify and error is None:
        for value in values:
            verification, _ = step('verify', [VERIFY, directory / value['certificate']], args.host)
            accepted = (verification['exit_code'] == 0 and
                        verification['output'].startswith('ACCEPT: '))
            value['verified'] = accepted
            lines = verification['output'].splitlines()
            value['verdict'] = lines[0] if lines else ''
            verifications.append({**verification, 'certificate': value['certificate']})
        if not all(v['verified'] for v in values):
            error = 'a certificate was rejected'

    meta = {
        'evaluator': args.evaluator, 'native_index': args.n,
        'threads': (args.threads or 1) if args.evaluator == 'first_crossing_optimized' else None,
        'threads_effective': (min(args.threads or 1, MAX_WORKERS)
                              if args.evaluator == 'first_crossing_optimized' else None),
        'cert': args.cert, 'verify': args.verify,
        'verified': (error is None and all(v['verified'] for v in values)) if verify else None,
        'values': values, 'error': error,
        'revision': report['revision'], 'dirty': report['dirty'],
        'binaries': {'meanders': sha256(MEANDERS),
                     'verify': sha256(VERIFY) if verify else None},
        'toolchains': {
            'rustc': subprocess.check_output(['rustc', '--version'], text=True).strip(),
            'lean': (ROOT / 'lean-toolchain').read_text().strip(),
        },
        'host': args.host, 'platform': platform.platform(), 'machine': platform.machine(),
        'cpu_count': report['cpu_count'], 'timestamp': timestamp.isoformat(timespec='microseconds'),
        'production': production, 'verifications': verifications,
    }
    (directory / 'meta.json').write_text(json.dumps(meta, indent=2) + '\n')
    for value in values:
        state = {None: 'not verified', True: 'ACCEPT', False: 'REJECT'}[value['verified']]
        print(f"{value['problem']}({value['n']}) = {value['count']}  [{value['profile']}, {state}]")
    if error:
        sys.exit(error)


if __name__ == '__main__':
    main()
