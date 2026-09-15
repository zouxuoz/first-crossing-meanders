#!/usr/bin/env python3
"""Measure one command's wall time and peak RSS on Linux or macOS (no build time).

Example: scripts/measure.py --host m2max --repeat 3 --output result.json -- ./program arg
Each sample is a fresh child process; RSS includes that process's threads,
not separately spawned processes. Run built executables, not build wrappers.
`--host` is a short stable label for the machine (letters, digits, hyphens)
recorded in the report.
Each sample keeps the child's output (first 4 KiB) so a report also records
what the program printed, and the report hashes the executable it ran.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
import time

OUTPUT_LIMIT = 4096
HOST_LABEL = re.compile(r'[a-z0-9][a-z0-9-]*')


def git_state():
    """Revision and dirty flag."""
    return {
        'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'dirty': bool(subprocess.check_output(
            ['git', 'status', '--porcelain'])),
    }


def executable_sha256(command):
    path = Path(command[0])
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def host_info(host):
    return {
        'host': host, 'platform': platform.platform(), 'machine': platform.machine(),
        'cpu_count': os.cpu_count(),
    }


def sample(command):
    """Run one fresh child, returning its sample and its captured output."""
    with tempfile.TemporaryFile() as log:
        start = time.perf_counter()
        with subprocess.Popen(command, stdout=log, stderr=log) as child:
            _, status, usage = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)
        wall = time.perf_counter() - start
        log.seek(0)
        output = log.read()
    return {
        'wall_seconds': wall,
        'peak_rss_bytes': usage.ru_maxrss * (1 if sys.platform == 'darwin' else 1024),
        'exit_code': child.returncode,
        'output': output[:OUTPUT_LIMIT].decode(errors='replace'),
    }, output


def measure(command, host, repeat=3, echo=None):
    """A complete report: git state, host, executable hash, and `repeat`
    fresh samples, stopping at the first failure."""
    report = {**git_state(), **host_info(host),
              'executable_sha256': executable_sha256(command), 'command': command, 'samples': []}
    for _ in range(repeat):
        entry, output = sample(command)
        report['samples'].append(entry)
        if echo:
            echo(entry)
        if entry['exit_code']:
            sys.stderr.write(output.decode(errors='replace'))
            break
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--host', required=True,
                        help='short machine label, e.g. m2max')
    parser.add_argument('--repeat', type=int, default=3)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command[:1] == ['--']:
        command = command[1:]
    if not command or args.repeat < 1:
        parser.error('provide a command and a positive repeat count')
    if not HOST_LABEL.fullmatch(args.host):
        parser.error('--host must be lowercase letters, digits and hyphens')
    if platform.system() not in ('Darwin', 'Linux'):
        parser.error('peak RSS units are supported on macOS and Linux only')
    report = measure(command, args.host, args.repeat,
                     echo=lambda s: print(json.dumps({k: v for k, v in s.items() if k != 'output'}), flush=True))
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    return int(any(s['exit_code'] for s in report['samples']))


if __name__ == '__main__':
    sys.exit(main())
