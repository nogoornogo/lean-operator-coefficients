#!/usr/bin/env python3
"""Check source snapshots and absence of retired closed certificates from imports.

This audits retirement integrity only; it never invokes Lean or verifies a
numerical theorem. All file reads are local and no generated output is saved.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / 'docs/topics/sm-computable-characters/archive'
retired = set()
count = 0
for name in ('q18-numerical', 'remaining-numerical'):
    folder = ARCHIVE / name
    manifest = json.loads((folder / 'manifest.json').read_text())
    for row in manifest['files']:
        snapshot = folder / row['snapshot']
        assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == row['sha256'], snapshot
        count += 1
        # The older manifest also keeps consumer/audit context snapshots.
        inactive = row.get('retired_module', '/SMNeutralCertificates/' in row['original'])
        if inactive:
            original = ROOT / row['original']
            assert not original.exists(), f'retired source restored: {original}'
            retired.add(row['original'][:-5].replace('/', '.'))

paths = [ROOT / (name + '.lean') for name in ('Math', 'Physics', 'GUT')]
for name in ('Math', 'Physics', 'GUT'):
    paths.extend((ROOT / name).rglob('*.lean'))
for path in paths:
    for imported in re.findall(r'^import\s+([\w.]+)', path.read_text(), flags=re.M):
        assert imported not in retired, f'{path}: retired import {imported}'
print(f'{count} snapshot hashes; {len(retired)} retired modules absent; active imports OK')
