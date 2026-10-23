#!/usr/bin/env python3
"""Replay the frozen mechanical migration in /tmp and compare source contents.

No repository source or index is written. This separates the reviewed move/
namespace transformation from the small manually reviewed compatibility controls.
The creation checkpoint of the frozen plan supplies checksum-guarded inputs.
"""
import io
import hashlib
import json
import shutil
import subprocess
import tarfile
import tempfile
import sys
from pathlib import Path
from source_api_registry import load_plan
from source_additions import reviewed_additions
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'lean-memory'))
from rewrite_registry import load_rewrites, apply_rewrites

ROOT = Path.cwd()
PLAN = 'docs/topics/source-api-compatibility/layout-plan.json'
baseline = subprocess.check_output(
    ['git', 'log', '--diff-filter=A', '--format=%H', '--', PLAN], text=True).splitlines()
if len(baseline) != 1:
    raise SystemExit('The frozen-plan creation checkpoint is not unique')
paths = ['Math', 'Physics', 'GUT', 'Math.lean', 'Physics.lean', 'GUT.lean', PLAN,
         'tools/layout/source-map.json']
archive = subprocess.check_output(['git', 'archive', baseline[0], *paths])
work = Path(tempfile.mkdtemp(prefix='source-api-review-'))
with tarfile.open(fileobj=io.BytesIO(archive)) as stream:
    stream.extractall(work, filter='data')
for file in ['tools/layout/source-api-apply.py', 'tools/layout/check-layout.mjs',
             'tools/layout/source_api_registry.py']:
    shutil.copyfile(ROOT / file, work / file)
for file in ['docs/topics/source-api-compatibility/proof-repairs.json',
             'docs/topics/source-api-compatibility/execution-repairs.json',
             'docs/topics/source-api-compatibility/namespace-repairs.json',
             'docs/topics/source-api-compatibility/registry-addendum.json',
             'tools/layout/source-api-repairs.py']:
    shutil.copyfile(ROOT / file, work / file)
# These utility/consumer files have their own explicit code review and focused
# builds; they are outside the pre-migration source snapshot.
controls = ['Math/Lean/Compatibility.lean',
            'Physics/Compatibility/Audit/AbelianMassSpectrum.lean',
            'Physics/Compatibility/Audit/Structures.lean',
            'Physics/Compatibility/Audit/LegacyInputs.lean',
            'GUT/Compatibility/Audit/LegacyRestriction.lean']
for file in controls:
    (work / file).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / file, work / file)
result = subprocess.run(['python3', 'tools/layout/source-api-apply.py'], cwd=work,
                        capture_output=True, text=True)
if result.returncode:
    raise SystemExit(result.stdout + result.stderr)
plan = load_plan(ROOT)
for record in load_rewrites(ROOT):
    file = work / record['canonical']
    file.write_text(apply_rewrites(file.read_text(), record))
source_paths = {p[k] for p in plan['paths'] for k in ['old', 'new']} | set(controls)
# The bounded structural pilot adds these checksum-guarded, separately audited
# modules; every older source still undergoes exact migration/proof replay.
addition_files = ['source-additions.json', 'remaining-source-additions.json']
added_sources = set()
for filename in addition_files:
    addition_path = ROOT/'docs/topics/higgs-cubature-structure'/filename
    if not addition_path.exists():
        continue
    additions = json.loads(addition_path.read_text())
    expected_kind = ('remaining-family-structural-cubature' if filename.startswith('remaining-')
                     else 'one-family-structural-cubature')
    assert additions['kind'] == expected_kind and additions['aggregate'] == 'Math.lean'
    for file, checksum in additions['sources'].items():
        assert file.startswith('Math/Algebra/HiggsFourWaveCubature/Structural/') and file.endswith('.lean')
        assert file not in source_paths and not (work/file).exists()
        assert hashlib.sha256((ROOT/file).read_bytes()).hexdigest() == checksum
        (work/file).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/file, work/file)
        source_paths.add(file)
        added_sources.add(file)
    assert set(additions['imports']) == {'import '+f[:-5].replace('/', '.') for f in additions['sources']}
    aggregate = work/additions['aggregate']
    aggregate.write_text(aggregate.read_text()+'\n'+'\n'.join(additions['imports'])+'\n')

# Later algebraic children are additive to the frozen refactor. Match each
# source hash and every owned aggregate import; do not ignore extra imports.
for topic in ['su6-protection-feasibility', 'model-input-connections']:
    if not (ROOT/'docs/topics'/topic/'source-additions.json').exists():
        continue
    sources, imports = reviewed_additions(ROOT, topic, source_paths)
    for file in sources:
        assert not (work/file).exists(), file
        (work/file).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/file, work/file)
        source_paths.add(file)
        added_sources.add(file)
    for file, lines in imports.items():
        aggregate = work/file
        aggregate.write_text(aggregate.read_text()+'\n'+'\n'.join(lines)+'\n')

for repair in json.loads((ROOT / 'docs/topics/source-api-compatibility/proof-repairs.json').read_text()):
    source_paths.add(repair['definitions'])
different = [f for f in sorted(source_paths) if (ROOT / f).read_bytes() != (work / f).read_bytes()]
for root in ['Math', 'Physics', 'GUT']:
    # Only import order differs for an appended consumer; there are no statements.
    file = root + '.lean'
    actual = [s for s in (ROOT / file).read_text().splitlines() if s.strip()]
    expected = [s for s in (work / file).read_text().splitlines() if s.strip()]
    actual_other = [s for s in actual if not s.startswith('import ')]
    expected_other = [s for s in expected if not s.startswith('import ')]
    if (actual_other != expected_other or any(not s.startswith('--') for s in actual_other)
            or set(actual) != set(expected)):
        different.append(file)
    elif len(actual) != len(set(actual)):
        different.append(file)
    source_paths.add(file)
if different:
    Path('/tmp/source-api-transform-differences.json').write_text(json.dumps(different, indent=2) + '\n')
    raise SystemExit(f'{len(different)} source contents differ from the reviewed transformation; see /tmp/source-api-transform-differences.json')
changed = subprocess.check_output(['git', 'status', '--porcelain', '-z', '--untracked-files=all']).decode().split('\0')
reviewed = sorted(s[3:] for s in changed if s and s[3:] in source_paths)
unexpected = [s[3:] for s in changed if s and s[3:].endswith('.lean')
              and s[3:].split('/')[0] in ['Math', 'Physics', 'GUT'] and s[3:] not in source_paths]
if unexpected:
    raise SystemExit(f'Unregistered source changes require separate review: {unexpected}')
Path('/tmp/source-api-reviewed-source-paths.json').write_text(json.dumps(reviewed, indent=2) + '\n')
added_count = len(added_sources)
frozen_count = len(source_paths)-len(controls)-3-added_count
print(f'{frozen_count} frozen source paths match the checksum-guarded replay; '
      f'{len(controls)} utility/consumer files and {added_count} checksum-guarded source additions '
      'require separate review; aggregate imports match')
print(f'{len(reviewed)} changed source paths identified for review; no unregistered library source changes')
print(f'Review copy: {work}')
