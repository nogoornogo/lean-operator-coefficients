#!/usr/bin/env python3
"""Regression checks for the mechanical source migration, independent of Lean."""
import importlib.util
import unittest
from pathlib import Path


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(file))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


apply = load('source_api_apply', 'source-api-apply.py')
plan = load('source_api_plan', 'source-api-plan.py')


class MigrationTests(unittest.TestCase):
    def test_code_boundaries(self):
        original = 'GUT.X /- GUT.Y /- nested -/ GUT.Z -/ "GUT.S\\\"T" -- GUT.U\nGUT.V'
        changed = apply.code_map(original, lambda s: s.replace('GUT', 'Physics'))
        self.assertEqual(changed, 'Physics.X /- GUT.Y /- nested -/ GUT.Z -/ "GUT.S\\\"T" -- GUT.U\nPhysics.V')

    def test_original_import_exclusion(self):
        original = ('run_cmd do\n  for mod in env.header.moduleNames do\n'
                    '    let mod := SourceLayout.originalModule mod\n'
                    '    if (`GUT.SU5).isPrefixOf mod then\n'
                    '      throwError "bad import"\n  let names := [`GUT.Actual]\n')
        masked, saved = apply.protect_module_audits(original)
        changed = masked.replace('GUT', 'Physics')
        for key, text in saved:
            changed = changed.replace(key, text)
        self.assertIn('(`GUT.SU5).isPrefixOf mod', changed)
        self.assertIn('let names := [`Physics.Actual]', changed)

    def test_ownership_layers_and_pilot_destination(self):
        for file in ('Math/RepresentationTheory/ProhibitionInput.lean',
                     'Physics/FieldTheory/Jets/WeylHiggsCurrent.lean',
                     'GUT/SU5/SelectionRules/SelectionRule.lean'):
            self.assertEqual(plan.target(file).split('/')[0], file.split('/')[0])
        self.assertEqual(plan.target('Physics/FieldTheory/Mass/AbelianMassSpectrum.lean'),
                         'Physics/FieldTheory/Mass/Spectrum/AbelianMassSpectrum.lean')


if __name__ == '__main__':
    unittest.main()
