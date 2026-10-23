#!/usr/bin/env python3
"""Post-build ownership and facade coverage check; not a replacement for Lean."""
import json
import re
from collections import Counter
from pathlib import Path
from source_api_registry import load_plan, bridge_source


def module(file):
    return str(Path(file).with_suffix('')).replace('/', '.')


def main():
    plan = load_plan()
    moved = {module(p['old']): module(p['new']) for p in plan['paths'] if p['old'] != p['new']}
    bridges = {b['old']: b for b in plan.get('importBridges', [])}
    legacy_modules = set(moved) | {module(b) for b in bridges}
    entries = {}
    repairs = json.loads(Path('docs/topics/source-api-compatibility/proof-repairs.json').read_text())
    for e in plan['entries']:
        entries.setdefault(e['module'], []).append(e)
    checked, alias_count = 0, 0
    ownership_differences = []
    paths = plan['paths'] + [dict(old=r['definitions'], new=r['definitions']) for r in repairs]
    for p in paths:
        old, canonical = module(p['old']), module(p['new'])
        source = Path(p['new']).read_text()
        data = json.loads((Path('.lake/build/lib/lean') / Path(p['new']).with_suffix('.ilean')).read_text())
        if data['module'] != canonical:
            raise SystemExit(f'Stale canonical metadata: {canonical}')
        if p['new'] in bridges:
            if source != bridge_source(bridges[p['new']], plan['migration']) or data['decls']:
                raise SystemExit(f'Legacy import carrier changed: {p["new"]}')
            if entries.get(old):
                raise SystemExit('An import carrier cannot hide protected declaration checks')
            checked += 1
            continue
        if any(dep in legacy_modules for dep in re.findall(r'^import ([\w.]+)', source, re.M)):
            raise SystemExit(f'Canonical implementation imports a legacy facade: {p["new"]}')
        if canonical.startswith('Physics.'):
            owned = set(data['decls'])
            for key, locations in data['references'].items():
                c = json.loads(key).get('c', {})
                if c.get('m') == canonical and locations.get('definition') is not None:
                    owned.add(c['n'])
            legacy = [n for n in owned if n.startswith('GUT.') or
                      re.search(r'^_private\..*\.GUT\.', n)]
            if legacy:
                raise SystemExit(f'Physics implementation retains GUT declarations: {legacy[:3]}')
        if old in moved:
            facade = Path(p['old']).read_text()
            if f'import {canonical}\n' not in facade or 'deprecated_module' not in facade:
                raise SystemExit(f'Missing deprecated import facade: {old}')
            old_data = json.loads((Path('.lake/build/lib/lean') / Path(p['old']).with_suffix('.ilean')).read_text())
            declared = set(old_data['decls'])
            # Elaborator-generated aliases are indexed as definition references;
            # ordinary source declarations additionally occur in `decls`.
            for key, locations in old_data['references'].items():
                c = json.loads(key).get('c', {})
                if c.get('m') == old and locations.get('definition') is not None:
                    declared.add(c['n'])
            target_refs = {json.loads(key).get('c', {}).get('n'): json.loads(key).get('c', {}).get('m')
                           for key in old_data['references']}
            for e in entries.get(old, []):
                if e['old'] not in declared:
                    raise SystemExit(f'Missing compiled legacy name: {e["old"]}')
                owner = canonical
                for repair in repairs:
                    if e['module'] == repair['originalModule'] and e['new'] != repair['theorem']:
                        owner = module(repair['definitions'])
                        owner = repair.get('generatedEquationOwners', {}).get(e['new'], owner)
                if target_refs.get(e['new']) != owner:
                    ownership_differences.append(dict(symbol=e['new'], kind=e['kind'],
                        expected=owner, actual=target_refs.get(e['new'])))
                if facade.count(f'assert_compatible {e["old"]} => {e["new"]}\n') != 1:
                    raise SystemExit(f'Alias is not covered by strict compile-time checks: {e["old"]}')
                alias_count += 1
            checked += 1
    if alias_count != len(plan['entries']):
        raise SystemExit('Protected alias inventory is incomplete')
    if ownership_differences:
        Path('/tmp/source-api-target-owner-differences.json').write_text(
            json.dumps(ownership_differences, indent=2) + '\n')
        raise SystemExit(f'{len(ownership_differences)} target ownership records need review; '
                         'see /tmp/source-api-target-owner-differences.json')
    counts = Counter(str(Path(p['new']).parent) for p in paths)
    print(f'{checked} deprecated import facades; {alias_count} protected aliases; canonical imports and Physics ownership OK')
    print('Largest implementation directory:', counts.most_common(1)[0])


if __name__ == '__main__':
    main()
