#!/usr/bin/env python3
"""Compare existing strict-audit count messages before and after relocation.

Supplementary inventory regression; actual Lean audits remain authoritative.
"""
import argparse
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path
from source_api_registry import load_plan
from audit_inventory import count_message_matches, inventory_name_allowed

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('baseline', type=Path)
parser.add_argument('rebuilt', type=Path)
parser.add_argument('--baseline-constants', type=Path)
parser.add_argument('--rebuilt-constants', type=Path)
args = parser.parse_args()
plan = load_plan()
moves = {p['old']: p['new'] for p in plan['paths']}


def inventory(file, migrate):
    result = defaultdict(list)
    for line in file.read_text().splitlines():
        match = re.match(r'info: ([^:]+\.lean):\d+:\d+: (.*strict.*)', line)
        if not match:
            continue
        source, message = match.groups()
        counts = tuple(map(int, re.findall(r'\d+', message)))
        if counts:
            result[moves.get(source, source) if migrate else source].append(counts)
    return dict(result)


before, after = inventory(args.baseline, True), inventory(args.rebuilt, False)
different = {f: dict(before=n, after=after.get(f)) for f, n in before.items() if after.get(f) != n}
# Namespace-wide audits enumerate compiler auxiliaries as well as public names.
# Synchronous elaboration can change their sharing/numbers. Reconcile only the
# exact recorded inventories, never skip an audit or lower its axiom allowlist.
records = json.loads(Path('docs/topics/source-api-compatibility/audit-inventory-repairs.json').read_text())
child_records = Path('docs/topics/proof-memory-audit/audit-inventory-repairs.json')
if child_records.exists():
    records += json.loads(child_records.read_text())
structural_records = Path('docs/topics/higgs-cubature-structure/audit-inventory-repairs.json')
if structural_records.exists():
    records += json.loads(structural_records.read_text())
if records and (args.baseline_constants is None or args.rebuilt_constants is None):
    raise SystemExit('Supply both constant snapshots to verify recorded compiler-helper count changes')
old_constants = {r['name'].replace('GUT.', 'Physics.', 1): r
                 for r in json.loads(args.baseline_constants.read_text())}
new_constants = {r['name']: r for r in json.loads(args.rebuilt_constants.read_text())}
protected = {e['new'] for e in plan['entries']}
reconciled = 0
for record in records:
    extension = record['kind'] == 'source-extension-and-helper-reconciliation'
    assert extension or record['kind'] == 'compiler-helper-count-reconciliation'
    extension_modules = set()
    if extension:
        addition_sources = {}
        for filename in ['source-additions.json', 'remaining-source-additions.json']:
            manifest = Path('docs/topics/higgs-cubature-structure')/filename
            if manifest.exists():
                sources = json.loads(manifest.read_text())['sources']
                assert not set(sources).intersection(addition_sources)
                addition_sources.update(sources)
        assert set(record['newSources']) == set(addition_sources)
        for source in record['newSources']:
            assert hashlib.sha256(Path(source).read_bytes()).hexdigest() == addition_sources[source]
        extension_modules = {s[:-5].replace('/', '.') for s in record['newSources']}
    file = record['audit']
    if file not in different:
        raise SystemExit(f'Unused compiler-helper reconciliation: {file}')
    if extension:
        # The existing foundation audit rejects Physics/GUT imports. Six later
        # Physics extensions share the Math object namespace in the global
        # export, but are absent from that Math-only audit environment.
        assert record['ownerLayer'] == 'Math' and file.startswith('Math/')
    def select(constants):
        return {n for n, info in constants.items()
                if any(n.startswith(p + '.') for p in record['prefixes'])
                and (not extension or info['module'].startswith(record['ownerLayer']+'.'))}
    old_names, new_names = select(old_constants), select(new_constants)
    removed, added = old_names-new_names, new_names-old_names
    for label, names in [('removed', removed), ('added', added)]:
        fingerprint = hashlib.sha256(json.dumps(sorted(names), separators=(',', ':')).encode()).hexdigest()
        if len(names) != record[label+'Count'] or fingerprint != record[label+'SHA256']:
            raise SystemExit(f'Compiler-helper inventory drift: {file}: {label}')
        for name in names:
            # Newly declared structural results are reviewed against their exact
            # source/owner manifest and strict module-wide Lean audit, not called
            # compiler helpers. Existing source-declared names cannot disappear.
            if not inventory_name_allowed(name, label, new_names, new_constants,
                                          protected, extension_modules):
                raise SystemExit(f'Non-helper or unaudited parent in count reconciliation: {name}')
    if (len(old_names) != record['baselineCount'] or len(new_names) != record['rebuiltCount']
            or (old_names & protected) - new_names):
        raise SystemExit(f'Public declaration loss or count drift: {file}')
    if not count_message_matches(before[file], after[file], record,
                                 len(old_names), len(new_names)):
        raise SystemExit(f'Audit messages changed beyond the exact inventory count: {file}')
    del different[file]
    reconciled += 1
if different:
    Path('/tmp/source-api-audit-count-differences.json').write_text(json.dumps(different, indent=2) + '\n')
    raise SystemExit(f'{len(different)} audit count records require review: /tmp/source-api-audit-count-differences.json')
print(f'{len(before)} existing strict-audit count records verified; '
      f'{reconciled} exact helper/source-extension inventory reconciliations; all old public parents retained')
