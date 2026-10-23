"""Reject unreviewed sources and aggregate imports in additive-topic replay."""
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from source_additions import reviewed_additions


class AdditionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root/'Math/Example.lean'
        self.source.parent.mkdir()
        self.source.write_text('theorem example : True := by trivial\n')
        self.manifest = self.root/'docs/topics/control/source-additions.json'
        self.manifest.parent.mkdir(parents=True)
        self.record = dict(kind='control', sources={'Math/Example.lean':
            hashlib.sha256(self.source.read_bytes()).hexdigest()},
            imports={'Math.lean': ['import Math.Example']})

    def load(self, known=()):
        self.manifest.write_text(json.dumps(self.record))
        return reviewed_additions(self.root, 'control', set(known))

    def test_verified_addition_cannot_replace_frozen_source(self):
        self.assertEqual(self.load()[1], self.record['imports'])
        with self.assertRaisesRegex(ValueError, 'replace an existing'):
            self.load(['Math/Example.lean'])

    def test_changed_proof_is_not_accepted_as_an_addition(self):
        self.source.write_text('axiom example : False\n')
        with self.assertRaisesRegex(ValueError, 'checksum changed'):
            self.load()

    def test_extra_missing_duplicate_or_wrong_layer_import_is_rejected(self):
        for imports in [[], ['import Physics.Example'],
                        ['import Math.Example', 'import Math.Unreviewed'],
                        ['import Math.Example', 'import Math.Example']]:
            self.record['imports'] = {'Math.lean': imports}
            with self.assertRaisesRegex(ValueError, 'aggregate imports'):
                self.load()
        self.record['imports'] = {'Physics.lean': ['import Math.Example']}
        with self.assertRaisesRegex(ValueError, 'aggregate imports'):
            self.load()

    def test_wrong_topic_and_path_escape_are_rejected(self):
        self.record['kind'] = 'other'
        with self.assertRaisesRegex(ValueError, 'Wrong or empty'):
            self.load()
        self.record['kind'] = 'control'
        self.record['sources'] = {'../Math/Example.lean': 'unreviewed'}
        with self.assertRaisesRegex(ValueError, 'Invalid added source path'):
            self.load()


if __name__ == '__main__':
    unittest.main()
