#!/usr/bin/env python3
"""Regression checks for snapshot-only navigation and metadata validation."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def module(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + '.py'))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


class PortableDocs(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.topics = self.root / 'docs/topics'
        (self.topics / '_history').mkdir(parents=True)
        (self.topics / 'sample').mkdir()
        (self.topics / 'sample/README.md').write_text('# Sample\n')
        (self.topics / 'README.md').write_text('[Sample](sample/README.md)\n')
        self.volume = self.topics / '_history/001_topics_history.md'
        self.volume.write_text('- [Sample](../sample/): verified scoped result\n')
        (self.root / 'AGENTS.md').write_text('')
        (self.root / 'README.md').write_text('')
        self.policy = self.root / 'policy.json'
        self.policy.write_text(json.dumps({
            'external_revisions': {'library': 'a1234567'},
            'publication_dates': {'docs/source.md': ['2000-01-01']}}))
        self.navigation = module('check-topic-index')
        self.metadata = module('check-work-metadata')
        self.metadata.ROOT = self.root
        self.metadata.POLICY = self.policy

    def metadata_check(self):
        with contextlib.redirect_stdout(io.StringIO()):
            self.metadata.main()

    def test_snapshot_without_git_or_migration_inventory(self):
        self.assertFalse((self.root / '.git').exists())
        self.assertEqual(self.navigation.check(self.topics, set()), (1, 1))
        self.metadata_check()

    def test_source_metadata_and_measurements_survive(self):
        (self.root / 'docs/source.md').write_text(
            'Library a1234567; publication 2000-01-01; 5130916 KiB.\n')
        self.metadata_check()

    def test_no_checkpoint_document_exemption(self):
        (self.root / 'docs/checkpoint.md').write_text('Checked 2000-01-01.\n')
        with self.assertRaises(SystemExit):
            self.metadata_check()

    def test_local_revisions_and_base_fields_rejected(self):
        for text in ('commit b1234567', 'merged as `12345678`', '- Base commit: unassigned'):
            with self.subTest(text=text):
                (self.root / 'README.md').write_text(text)
                with self.assertRaises(SystemExit):
                    self.metadata_check()

    def test_dated_filename_rejected(self):
        (self.root / 'docs/record-2000-01-01.md').write_text('Checkpoint\n')
        with self.assertRaises(SystemExit):
            self.metadata_check()

    def test_missing_subject_and_outcome_links_rejected(self):
        for target in (self.topics / 'README.md', self.volume):
            original = target.read_text()
            target.write_text('')
            with self.assertRaises(ValueError):
                self.navigation.check(self.topics, set())
            target.write_text(original)

    def test_outcome_volume_order_and_format_rejected(self):
        self.volume.rename(self.volume.with_name('002_topics_history.md'))
        with self.assertRaisesRegex(ValueError, 'nonsequential'):
            self.navigation.check(self.topics, set())
        self.volume.with_name('002_topics_history.md').rename(self.volume)
        self.volume.write_text('- [Sample](../sample/)\n')
        with self.assertRaisesRegex(ValueError, 'malformed'):
            self.navigation.check(self.topics, set())


if __name__ == '__main__':
    unittest.main()
