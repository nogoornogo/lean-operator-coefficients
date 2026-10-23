#!/usr/bin/env python3
"""Run source producers without writes; check canonical targets/imports/content."""
import contextlib
import io
import json
import re
import runpy
from pathlib import Path
from unittest.mock import patch
from source_api_registry import load_plan

ROOT = Path.cwd()
plan = load_plan()
facades = {p['old'] for p in plan['paths'] if p['old'] != p['new']}
legacy_modules = {p[:-5].replace('/', '.') for p in facades}
scripts = [
    'generate-colored-quartic-source.py', 'generate-quartic-source.py',
    'generate-higgs-first-control.py', 'generate-weyl-direction-control.py',
    'generate-rank-four-control.py', 'generate-scalar-cubature.py',
    'generate-higgs-cubature.py', 'generate-higgs-collinear-structure.py',
    'generate-higgs-remaining-structure.py',
]
outputs = {}


def capture(path, text, *args, **kwargs):
    outputs[str(path.resolve().relative_to(ROOT))] = text
    return len(text)


with patch.object(Path, 'write_text', capture), patch.object(Path, 'mkdir', lambda *a, **k: None):
    for script in scripts:
        with contextlib.redirect_stdout(io.StringIO()):
            runpy.run_path(str(Path('tools/derivative-literature') / script), run_name='__main__')
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        runpy.run_path('tools/structural-support/finite-charge-witnesses.py', run_name='__main__')
    outputs['Physics/StandardModel/Operators/Support/Lepton/SMLeptonChargeWitnesses.lean'] = output.getvalue()

different = []
for file, generated in outputs.items():
    if file in facades:
        raise SystemExit(f'Generator would overwrite legacy facade: {file}')
    if not Path(file).exists():
        raise SystemExit(f'Generator target is not a canonical source: {file}')
    if any(m in legacy_modules for m in re.findall(r'^import ([\w.]+)', generated, re.M)):
        raise SystemExit(f'Generator uses a deprecated implementation dependency: {file}')
    if file.startswith('Physics/') and re.search(r'^namespace GUT(?:\.|\s|$)', generated, re.M):
        raise SystemExit(f'Generator would restore a canonical GUT namespace: {file}')
    if generated != Path(file).read_text():
        different.append(file)
if different:
    Path('/tmp/source-api-generator-differences.json').write_text(json.dumps(different, indent=2) + '\n')
    raise SystemExit(f'{len(different)} generated contents need review: /tmp/source-api-generator-differences.json')
print(f'{len(scripts)+1} generators; {len(outputs)} canonical source outputs reproduced exactly; no repository writes')
