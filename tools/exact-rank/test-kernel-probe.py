#!/usr/bin/env python3
"""Small process controls for the Linux guard; no Lean or large allocation."""
import argparse
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


sys.dont_write_bytecode = True
RUNNER = Path(__file__).with_name('kernel-probe.py').resolve()
SPEC = importlib.util.spec_from_file_location('kernel_probe', RUNNER)
PROBE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROBE)


class ProcessControls(unittest.TestCase):
    def run_control(self, program, *options):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake_lake = root / 'lake'
            fake_lake.write_text(f'#!{sys.executable}\n' + program + '\n')
            fake_lake.chmod(0o700)
            env = dict(os.environ, PATH=tmp + os.pathsep + os.environ['PATH'])
            result = subprocess.run(
                [sys.executable, str(RUNNER), *options, 'control', str(root / 'probe.log')],
                env=env, text=True, capture_output=True, timeout=20)
            return result

    def test_success(self):
        result = self.run_control('raise SystemExit(0)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_child_failure(self):
        result = self.run_control('raise SystemExit(7)')
        self.assertEqual(result.returncode, 7, result.stdout + result.stderr)

    def test_timeout(self):
        result = self.run_control('import time; time.sleep(60)', '--timeout-seconds', '0.05')
        self.assertEqual(result.returncode, 1)
        self.assertIn('wall-clock limit', result.stdout)

    def test_rss_stop(self):
        result = self.run_control(
            'import time; allocation = bytearray(1024 * 1024); time.sleep(60)',
            '--rss-limit-gib', '0.0001')
        self.assertEqual(result.returncode, 1)
        self.assertIn('group RSS limit', result.stdout)

    def test_stale_cache_refuses_build(self):
        result = self.run_control(
            "import sys; raise SystemExit(3 if '--no-build' in sys.argv else 0)",
            '--build', '--require-cached', 'closed.certificate')
        self.assertEqual(result.returncode, 1)
        self.assertIn('refusing launch: cache precondition failed', result.stdout)

    def test_ready_cache_preserves_build_result(self):
        result = self.run_control(
            "import sys; raise SystemExit(0 if '--no-build' in sys.argv else 7)",
            '--build', '--require-cached', 'closed.certificate')
        self.assertEqual(result.returncode, 7)

    def test_reserve_refuses_launch(self):
        with patch.object(sys, 'argv', ['probe', '--min-available-gib', '1', 'input', 'log']), \
                patch.object(PROBE, 'available_kib', return_value=1), \
                patch.object(PROBE.subprocess, 'Popen') as launch, \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(PROBE.main(), 1)
            launch.assert_not_called()

    def test_invalid_budgets(self):
        for value in ['0', '-1', 'nan', 'inf']:
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                PROBE.positive(value)


if __name__ == '__main__':
    unittest.main()
