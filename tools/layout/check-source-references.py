#!/usr/bin/env python3
"""Compare rebuilt symbol references to the saved pre-migration metadata.

This detects unexpected name resolution after adding namespace opens. It does
not prove theorem validity; kernel builds and strict axiom audits remain required.
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path
from source_api_registry import load_plan
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'lean-memory'))
from rewrite_registry import load_rewrites, baseline_ranges, rewritten_ranges


def module(file):
    return str(Path(file).with_suffix('')).replace('/', '.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('baseline_metadata', type=Path)
    args = parser.parse_args()
    baseline = json.loads(args.baseline_metadata.read_text())
    plan = load_plan()
    modules = {module(p['old']): module(p['new']) for p in plan['paths']}
    physics = set(plan['physicsOwned'])
    repairs = json.loads(Path('docs/topics/source-api-compatibility/proof-repairs.json').read_text())
    scheduling = {r['canonical'] for r in json.loads(
        Path('docs/topics/source-api-compatibility/execution-repairs.json').read_text())}
    proof_rewrites = {r['canonical']: r for r in load_rewrites()}
    scheduling.update(r['canonical'] for r in proof_rewrites.values() if r.get('execution'))
    exclusions = {}
    if proof_rewrites:
        commits = subprocess.check_output(['git', 'log', '--diff-filter=A', '--format=%H', '--',
            'docs/topics/source-api-compatibility/layout-plan.json'], text=True).splitlines()
        if len(commits) != 1:
            raise SystemExit('Frozen source checkpoint is not unique')
        for file, record in proof_rewrites.items():
            original = subprocess.check_output(['git', 'show', commits[0]+':'+record['baselineSource']], text=True)
            exclusions[file] = (baseline_ranges(original, record),
                                rewritten_ranges(Path(file).read_text(), record))

    def outside(pos, excluded):
        return not any(start <= pos[0] <= end for start, end in excluded)

    def current_owner(name, owner):
        for repair in repairs:
            if owner == repair['originalModule']:
                theorem = 'GUT.' + repair['theorem'][8:]
                if name != theorem:
                    canonical_name = 'Physics.' + name[4:] if name.startswith('GUT.') else name
                    return repair.get('generatedEquationOwners', {}).get(
                        canonical_name, module(repair['definitions']))
        return modules.get(owner, owner)

    def current_name(name, owner):
        if name.startswith('_private.' + owner + '.'):
            name = name.replace('_private.' + owner + '.', '_private.' + current_owner(name, owner) + '.', 1)
            if modules.get(owner, owner).startswith('Physics.'):
                name = name.replace('.GUT.', '.Physics.', 1)
            return name
        # Anonymous audit examples have transient generated names absent from
        # the exported public inventory; their defining Physics module still
        # fixes ownership. Compare their renamed references rather than omit them.
        if modules.get(owner, owner).startswith('Physics.') and name.startswith('GUT.'):
            return 'Physics.' + name[4:]
        prefix = name
        while prefix.startswith('GUT.'):
            if prefix in physics:
                return 'Physics.' + name[4:]
            prefix = prefix.rsplit('.', 1)[0]
        return name

    def references(data, migrate, lines=None, excluded=()):
        result = set()
        for key, locations in data['references'].items():
            positions = locations['usages'] + ([locations['definition']] if locations['definition'] else [])
            if excluded and positions and not any(outside(p, excluded) for p in positions):
                continue
            if lines is not None:
                if not any(lines[0] <= p[0] <= lines[1] for p in positions):
                    continue
            c = json.loads(key).get('c')
            if not c or not c.get('m'):
                continue
            name, owner = c['n'], c['m']
            if migrate:
                target_owner = current_owner(name, owner)
                name = current_name(name, owner)
                owner = target_owner
            result.add((name, owner))
        return result

    def usage_sequence(data, migrate, lines=None, scheduling_option=False, excluded=()):
        events = set()
        for key, locations in data['references'].items():
            c = json.loads(key).get('c')
            if not c or not c.get('m'):
                continue
            name, owner = c['n'], c['m']
            if migrate:
                target_owner = current_owner(name, owner)
                name, owner = current_name(name, owner), target_owner
            for pos in locations['usages']:
                if outside(pos, excluded) and (lines is None or lines[0] <= pos[0] <= lines[1]):
                    events.add((*pos[:4], name, owner))
        if scheduling_option:
            options = [e for e in events if e[-2:] == ('Lean.Elab.async', 'Lean.CoreM')]
            if len(options) != 1:
                raise SystemExit(f'Unexpected scheduling-option usage count: {data["module"]}')
            events.difference_update(options)
        # Positions only determine order: imports/namespaces can add lines and
        # qualified replacements can change columns. Preserve every resolved
        # occurrence, not just the module-wide set of names.
        return [(e[-2], e[-1]) for e in sorted(events)]

    def compare_usages(file, expected, actual):
        if expected != actual:
            index = next((i for i, (a, b) in enumerate(zip(expected, actual)) if a != b),
                         min(len(expected), len(actual)))
            differences.append(dict(file=file, usageOrder=dict(index=index,
                expectedCount=len(expected), actualCount=len(actual),
                expected=expected[max(0,index-2):index+4],
                actual=actual[max(0,index-2):index+4])))

    differences = []
    count = 0
    for p in plan['paths']:
        if p['old'] == 'Math/Audit/ImportOrigin.lean':
            continue  # Its generated lookup table intentionally follows the moves.
        old = baseline[p['old']]
        new = json.loads((Path('.lake/build/lib/lean') / Path(p['new']).with_suffix('.ilean')).read_text())
        repair = next((r for r in repairs if r['canonical'] == p['new']), None)
        if repair:
            # Definitions retain their complete original references. The one
            # reviewed proof changes dependencies; compare its statement alone.
            basic = json.loads((Path('.lake/build/lib/lean') / Path(repair['definitions']).with_suffix('.ilean')).read_text())
            expected = references(old, True, (0, repair['baselinePrefixLines'] - 1))
            actual = references(basic, False)
            if expected != actual:
                differences.append(dict(file=repair['definitions'], missing=sorted(expected-actual), extra=sorted(actual-expected)))
            compare_usages(repair['definitions'],
                usage_sequence(old, True, (0, repair['baselinePrefixLines'] - 1)),
                usage_sequence(basic, False))
            source_lines = Path(p['new']).read_text().splitlines()
            start = next(i for i, line in enumerate(source_lines) if line.startswith('theorem fierz_blockAlternation'))
            end = next(i for i in range(start, len(source_lines)) if ':= by' in source_lines[i])
            expected = references(old, True, tuple(n-1 for n in repair['baselineStatementLines']))
            actual = references(new, False, (start, end))
            compare_usages(p['new'],
                usage_sequence(old, True, tuple(n-1 for n in repair['baselineStatementLines'])),
                usage_sequence(new, False, (start, end)))
        else:
            before_excluded, after_excluded = exclusions.get(p['new'], ((), ()))
            expected, actual = references(old, True, excluded=before_excluded), references(new, False, excluded=after_excluded)
            compare_usages(p['new'], usage_sequence(old, True, excluded=before_excluded),
                usage_sequence(new, False, scheduling_option=p['new'] in scheduling, excluded=after_excluded))
        if p['new'] in scheduling:
            # The recorded scheduling-only insertion names this option; every
            # original declaration/proof reference is still compared normally.
            expected.add(('Lean.Elab.async', 'Lean.CoreM'))
        missing, extra = expected - actual, actual - expected
        if missing or extra:
            differences.append(dict(file=p['new'], missing=sorted(missing), extra=sorted(extra)))
        count += 1
    if differences:
        Path('/tmp/source-api-reference-differences.json').write_text(json.dumps(differences, indent=2) + '\n')
        raise SystemExit(f'{len(differences)} modules need reference review; see /tmp/source-api-reference-differences.json')
    print(f'{count} canonical modules preserve elaborated reference sets and occurrence order outside exact reviewed proof bodies under the ownership/path map; '
          f'{len(repairs)} reviewed proof split(s) preserve all definition and statement references; '
          f'{len(scheduling)} recorded scheduling-option references; '
          f'{sum(len(r["changes"]) for r in proof_rewrites.values())} exact reviewed proof-body replacements')


if __name__ == '__main__':
    main()
