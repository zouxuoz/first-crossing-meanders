#!/usr/bin/env python3
"""Exercise recorded runs against the built Rust producer and Lean checker."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import evaluate


class EvaluateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='meanders evaluations ')
        self.addCleanup(self.temp.cleanup)
        self.work = Path(self.temp.name)

    def run_evaluator(self, *args, success=True):
        result = subprocess.run(
            [sys.executable, evaluate.ROOT / 'scripts/evaluate.py', '--host', 'test',
             '--out', 'runs', *args], cwd=self.work, capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def records(self):
        return [(p, json.loads(p.read_text())) for p in sorted(self.work.rglob('meta.json'))]

    def test_default_native_run(self):
        for evaluator in evaluate.EVALUATORS:
            with self.subTest(evaluator=evaluator):
                self.run_evaluator('--evaluator', evaluator, '--n', '2')
                _, meta = next((p, m) for p, m in self.records() if m['evaluator'] == evaluator)
                self.assertTrue(meta['verified'])
                self.assertEqual(meta['native_index'], 2)
                self.assertEqual({(v['problem'], v['n'], v['count']) for v in meta['values']},
                                 {('closed', 2, '2'), ('open', 4, '3'), ('open', 3, '2')})
                self.assertEqual(meta['cert'], 'auto')
                self.assertTrue(all(v['profile'] == 'full' for v in meta['values']))
                self.assertEqual(meta['revision'], subprocess.check_output(
                    ['git', 'rev-parse', 'HEAD'], cwd=evaluate.ROOT, text=True).strip())
                self.assertEqual(meta['threads'], 1 if evaluator.endswith('optimized') else None)
                self.assertEqual(meta['threads_effective'],
                                 1 if evaluator.endswith('optimized') else None)
                self.assertEqual(len(meta['verifications']), 3)
                self.assertGreater(meta['production']['peak_rss_bytes'], 0)
                self.assertEqual(len(meta['binaries']['meanders']), 64)

    def test_native_profiles_and_zero(self):
        for evaluator in evaluate.EVALUATORS:
            for cert, n in [('full', 2), ('compact', 2), ('count', 0)]:
                with self.subTest(evaluator=evaluator, cert=cert):
                    args = ['--evaluator', evaluator, '--n', str(n),
                            '--cert', cert, '--verify', 'always']
                    if evaluator.endswith('optimized'):
                        args += ['--threads', '2']
                    before = {p for p, _ in self.records()}
                    self.run_evaluator(*args)
                    path, meta = next((p, m) for p, m in self.records() if p not in before)
                    expected = {('closed', 2, '2'), ('open', 4, '3'), ('open', 3, '2')} if n else {
                        ('closed', 0, '0'), ('open', 0, '1')}
                    self.assertEqual({(v['problem'], v['n'], v['count']) for v in meta['values']}, expected)
                    self.assertTrue(meta['verified'])
                    for value in meta['values']:
                        self.assertTrue((path.parent / value['certificate']).is_file())
                        self.assertEqual(value['profile'], 'compact' if cert == 'count' else cert)
                        self.assertEqual(value['representation'],
                                         'count' if cert == 'count' else 'first-crossing-lower-jet')
                    self.assertEqual(bool(list(path.parent.glob('*.txt'))), cert == 'full')

    def test_skipped_verification_and_repeat_preserves_output(self):
        args = ['--evaluator', 'first_crossing', '--n', '2', '--cert', 'count', '--verify', 'never']
        self.run_evaluator(*args)
        original, _ = self.records()[0]
        contents = original.read_bytes()
        self.run_evaluator(*args)
        self.assertEqual(len(self.records()), 2)
        self.assertEqual(original.read_bytes(), contents)
        for _, meta in self.records():
            self.assertIsNone(meta['verified'])
            self.assertIsNone(meta['values'][0]['verified'])
            self.assertIsNone(meta['binaries']['verify'])
            self.assertEqual(meta['verifications'], [])

    def test_invalid_arguments_do_not_create_runs(self):
        for args in [('--evaluator', 'unknown'), ('--evaluator', 'brute_force'),
                     ('--n', '-1'), ('--threads', '-1'), ('--threads', '2')]:
            self.run_evaluator('--evaluator', 'first_crossing', '--n', '0', *args, success=False)
        self.assertFalse((self.work / 'runs').exists())

    def test_production_failure_retains_report(self):
        # Exceeds the CLI's machine-sized index, so production fails before counting.
        self.run_evaluator('--evaluator', 'first_crossing', '--n', str(2**64),
                           '--verify', 'never', success=False)
        _, meta = self.records()[0]
        self.assertNotEqual(meta['production']['exit_code'], 0)
        self.assertIn('production failed', meta['error'])
        self.assertEqual(meta['values'], [])

    def test_rejected_verification_is_not_recorded_as_acceptance(self):
        real_step = evaluate.step

        def reject(name, command, host):
            if name == 'verify':
                return {'name': name, 'command': [str(c) for c in command],
                        'exit_code': 1, 'output': 'REJECT: test verdict\n'}, {}
            return real_step(name, command, host)

        argv = ['evaluate.py', '--host', 'test', '--out', str(self.work),
                '--evaluator', 'first_crossing', '--n', '0', '--verify', 'always']
        cwd = Path.cwd()
        try:
            with patch.object(sys, 'argv', argv), patch.object(evaluate, 'step', reject), \
                    contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit):
                evaluate.main()
        finally:
            os.chdir(cwd)
        _, meta = self.records()[0]
        self.assertFalse(meta['verified'])
        self.assertFalse(meta['values'][0]['verified'])
        self.assertEqual(meta['error'], 'a certificate was rejected')


if __name__ == '__main__':
    unittest.main()
