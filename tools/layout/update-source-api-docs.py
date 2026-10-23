#!/usr/bin/env python3
"""Update current readers/source tools; retain topic checkpoint evidence."""
import json
import re
from collections import defaultdict
from pathlib import Path
from source_api_registry import load_plan

plan = load_plan()
paths = {p['old']: p['new'] for p in plan['paths'] if p['old'] != p['new']}
modules = {a[:-5].replace('/', '.'): b[:-5].replace('/', '.') for a, b in paths.items()}
direct = {e['old']: e['new'] for e in plan['entries']}
parents, shared = set(), set()
for names, dest in [(plan['physicsOwned'], parents), (plan['applicationOwned'], shared)]:
    for name in names:
        while '.' in name:
            name = name.rsplit('.', 1)[0]
            if name.startswith('GUT.'):
                dest.add(name)
pure = parents - shared


def rename(match):
    name = match.group()
    closing = ''
    while name.endswith("'") and name not in direct and name not in parents:
        name, closing = name[:-1], "'" + closing
    if name in direct:
        return direct[name] + closing
    prefix = name
    while '.' in prefix:
        if prefix in pure:
            return 'Physics.' + name[4:] + closing
        prefix = prefix.rsplit('.', 1)[0]
    return name + closing


docs = [Path('README.md')]
for root in ['docs/proof', 'docs/model-studies', 'docs/verification', 'docs/architecture']:
    docs.extend(Path(root).rglob('*.md'))
tools = [p for p in Path('tools').rglob('*') if p.suffix in ('.py', '.mjs', '.md')
         and 'layout' not in p.parts and 'probes' not in p.parts
         and p.name != 'connection-probe.py']  # Retained OLD-template diagnostic.
count = 0
parent_targets = defaultdict(set)
for p in plan['paths']:
    parent_targets[str(Path(p['old']).parent)].add(str(Path(p['new']).parent))
parent_moves = {old: next(iter(targets)) for old, targets in parent_targets.items()
                if len(targets) == 1 and old not in targets}
parent_modules = {a.replace('/', '.'): b.replace('/', '.') for a, b in parent_moves.items()}
for file in docs + tools:
    original = text = file.read_text()
    # Complete source paths move; module strings inside tool-generated Lean
    # keep their legacy reexports, while reflection/source readers use current
    # declarations. Existing temporary clients continue testing those routes.
    for old, new in paths.items():
        text = text.replace(old, new)
    if file in docs:
        text = re.sub(r'\b(?:Math|Physics)\.[\w.]+',
                      lambda m: modules.get(m[0], m[0]), text)
    text = re.sub(r'\bGUT(?:\.[\w\']+)+', rename, text)
    if file.name.startswith('generate-') and file.suffix == '.py':
        # Generators must reproduce canonical implementation imports/locations,
        # including targets assembled as directory / filename.
        def generated_module(match):
            name = match[0]
            if text[match.end():match.end()+1] == '.':
                return parent_modules.get(name, name)
            return modules.get(name, parent_modules.get(name, name))
        text = re.sub(r'\b(?:Math|Physics)(?:\.[\w]+)+', generated_module, text)
        for old, new in parent_moves.items():
            for quote in ("'", '"'):
                text = text.replace(quote + old + quote, quote + new + quote)
    if text != original:
        file.write_text(text)
        count += 1
print(f'Updated {count} current documents/tool sources; topic records retained')
