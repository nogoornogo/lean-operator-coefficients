"""Negative controls for inherited caches, stale artifacts and timed-out compilers."""
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('profile_project', Path(__file__).with_name('profile-project.py'))
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)


class ProfileControls(unittest.TestCase):
    def test_project_setup_is_relocated_and_external_dependencies_stay_pinned(self):
        graph = {'Physics.A': ['Math.B'], 'Math.B': []}
        data = dict(name='Physics.A', isModule=False,
                    importArts={'Math.B': [['/project/.lake/build/lib/lean/Math/B.olean']],
                                'Mathlib.X': [['/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/X.olean']]})
        result = json.loads(profile.relocate_setup(json.dumps(data), Path('/project/.lake/build'),
                            Path('/audit/artifacts'), 'Physics.A', graph))
        self.assertEqual(result['importArts']['Math.B'][0][0], '/audit/artifacts/lib/lean/Math/B.olean')
        self.assertEqual(result['importArts']['Mathlib.X'], data['importArts']['Mathlib.X'])
        data['importArts']['Math.B'] = [['/another/project-cache/Math/B.olean']]
        with self.assertRaisesRegex(ValueError, 'Inherited project artifact'):
            profile.relocate_setup(json.dumps(data), Path('/project/.lake/build'),
                                   Path('/audit/artifacts'), 'Physics.A', graph)

    def test_stale_dependency_or_changed_artifact_cannot_be_replayed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out = root/'Math/A.olean'
            out.parent.mkdir()
            out.write_bytes(b'measured compiler output')
            deps = {'Math.B': {'Math/B.olean': 'measured-parent-hash'}}
            row = dict(status='success', fingerprint='current-source-and-dependencies',
                       dependencyArtifacts=deps, artifacts={'Math/A.olean': profile.digest(out.read_bytes())})
            valid = lambda current=deps: profile.reusable_record(row, 'current-source-and-dependencies', [out], root, current)
            self.assertTrue(valid())
            self.assertFalse(valid({'Math.B': {'Math/B.olean': 'different-parent-hash'}}))
            out.write_bytes(b'inherited or modified output')
            self.assertFalse(valid())
            self.assertFalse(profile.reusable_record(row, 'changed-source', [out], root, deps))

    def test_timeout_is_failure_even_if_terminated_compiler_exits_zero(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script = ('import signal,time,sys\n'
                      'signal.signal(signal.SIGTERM, lambda *_: sys.exit(0))\n'
                      'print("compiler started", flush=True)\n'
                      'time.sleep(10)\n')
            result = profile.measured_compile([sys.executable, '-c', script], os.environ.copy(),
                                               root/'compiler.log', root, timeout=.3)
            self.assertEqual(result['exit'], 0)
            self.assertTrue(result['timeout'])
            self.assertFalse(profile.succeeded(result))
            self.assertGreater(result['peakResidentKiB'], 0)

    def test_only_requested_dependency_closure_is_selected(self):
        graph = {'GUT': ['Physics.A', 'Math.Unrelated'], 'Physics.A': ['Math.B'],
                 'Math.B': [], 'Math.Unrelated': []}
        self.assertEqual(profile.dependency_order(graph, ['Physics.A']), ['Math.B', 'Physics.A'])
        with self.assertRaises(ValueError):
            profile.dependency_order(graph, ['Missing'])

    def test_module_header_control_keeps_visibility_and_import_all(self):
        header = '/- header /- nested -/ -/\nmodule\npublic import Mathlib.X\nimport all Mathlib.X\n'
        source = header + '\n/- documentation\nimport NotAnImport\n-/\npublic section\ndef value := 1\n'
        self.assertEqual(profile.import_header(source), header)

    def test_logged_error_is_not_a_successful_compilation(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory)/'compiler.log'
            log.write_text('Probe.lean:1:1: error: declaration failed\n')
            self.assertTrue(profile.has_errors(log))
            self.assertFalse(profile.succeeded(dict(exit=0, timeout=False, reportedErrors=True)))

    def test_actual_compiler_imports_must_match_source_dependency_graph(self):
        graph = {'Physics.A': ['Math.B'], 'Math.B': [], 'Math.C': []}
        valid = dict(directImports=[['Math.B', False, False, False], ['Mathlib.X', False, False, False]])
        profile.check_project_imports(valid, 'Physics.A', graph)
        with self.assertRaisesRegex(ValueError, 'dependency graph disagreement'):
            profile.check_project_imports(dict(directImports=valid['directImports'] + [['Math.C', False, False, False]]),
                                          'Physics.A', graph)


if __name__ == '__main__':
    unittest.main()
