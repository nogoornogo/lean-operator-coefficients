"""Proof-review boundaries must not conceal changes to statements or neighbors."""
import unittest
from rewrite_registry import apply_rewrites, rewritten_ranges, baseline_ranges


class RewriteBoundaries(unittest.TestCase):
    source = 'theorem first : True := by\n  trivial\n\ntheorem second : True := by\n  trivial\n'
    record = dict(changes=[dict(statement='theorem first : True := by', before='  trivial',
                                after='  exact True.intro', baselineProofLines=[1, 1])])

    def test_repeated_body_in_neighbor_is_not_rewritten(self):
        new = apply_rewrites(self.source, self.record)
        self.assertIn('theorem second : True := by\n  trivial', new)
        self.assertEqual(rewritten_ranges(new, self.record), [[1, 1]])
        self.assertEqual(baseline_ranges(self.source, self.record), [[1, 1]])

    def test_a_changed_statement_is_rejected(self):
        with self.assertRaises(ValueError):
            apply_rewrites(self.source.replace('first : True', 'first : False'), self.record)

    def test_unowned_or_incorrect_baseline_range_is_rejected(self):
        bad = dict(changes=[dict(self.record['changes'][0], baselineProofLines=[0, 4])])
        with self.assertRaises(ValueError):
            baseline_ranges(self.source, bad)
        with self.assertRaises(ValueError):
            apply_rewrites(self.source, dict(changes=[dict(self.record['changes'][0], before='  missing')]))

    def test_scheduling_record_cannot_change_proof_or_limits(self):
        insertion = ('-- Check finite certificates sequentially to avoid blocked elaboration worker stacks.\n'
                     'set_option Elab.async false\n\n')
        record = dict(changes=[], execution=dict(marker='namespace Control\n', insertion=insertion))
        source = 'namespace Control\n' + self.source
        self.assertEqual(apply_rewrites(source, record), insertion + source)
        self.assertEqual(rewritten_ranges(insertion + source, record), [])
        general = ('-- Elaborate proofs sequentially to avoid blocked worker stacks.\n'
                   'set_option Elab.async false\n\n')
        general_record = dict(changes=[], execution=dict(record['execution'], insertion=general))
        self.assertEqual(apply_rewrites(source, general_record), general + source)
        bad = dict(changes=[], execution=dict(record['execution'], insertion='set_option maxHeartbeats 0\n'))
        with self.assertRaisesRegex(ValueError, 'Unreviewed execution-option'):
            apply_rewrites(source, bad)
        with self.assertRaisesRegex(ValueError, 'marker missing or ambiguous'):
            apply_rewrites(source + 'namespace Control\n', record)


    def test_preamble_is_exact_and_cannot_inject_declarations(self):
        header = 'import Old.Module\n\n'
        record = dict(changes=[], preamble=dict(before=header,after='import New.Module\n\n'))
        self.assertEqual(apply_rewrites(header+self.source, record),
                         'import New.Module\n\n'+self.source)
        with self.assertRaises(ValueError):
            apply_rewrites('import Wrong.Module\n\n'+self.source, record)
        for injection in ['set_option maxRecDepth 9999\n','axiom missing : False\n']:
            bad = dict(changes=[],preamble=dict(before=header,after=injection))
            with self.assertRaises(ValueError):
                apply_rewrites(header+self.source,bad)


if __name__ == '__main__':
    unittest.main()
