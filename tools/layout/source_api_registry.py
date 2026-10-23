"""Read the immutable migration plan and its reviewed ownership addendum."""
import json
from pathlib import Path


def load_plan(root=Path('.')):
    topic = Path(root) / 'docs/topics/source-api-compatibility'
    plan = json.loads((topic / 'layout-plan.json').read_text())
    file = topic / 'registry-addendum.json'
    if not file.exists():
        return plan
    extra = json.loads(file.read_text())
    by_old = {p['old']: p for p in plan['paths']}
    for move in extra['paths']:
        assert move['old'] in by_old and by_old[move['old']]['new'] == move['old']
        by_old[move['old']]['new'] = move['new']
    assert len({p['new'] for p in plan['paths']}) == len(plan['paths'])
    assert not ({e['old'] for e in extra['entries']} & {e['old'] for e in plan['entries']})
    plan['entries'] += extra['entries']
    plan['physicsOwned'] += extra['physicsOwned']
    reclassified = set(extra['physicsOwned'])
    plan['applicationOwned'] = [n for n in plan['applicationOwned'] if n not in reclassified]
    plan['physicsUsers'] = sorted(set(plan['physicsUsers']) | set(extra['physicsUsers']))
    plan['namespaceUsers'] = extra.get('namespaceUsers', {})
    plan['importBridges'] = extra.get('importBridges', [])
    return plan


def bridge_source(bridge, migration):
    """Render a declaration-free legacy import carrier, not a proof premise."""
    text = ''.join('import ' + module + '\n' for module in bridge['legacyImports'])
    message = 'Use ' + ' and '.join(bridge['canonicalImports']) + ' instead.'
    return (text + '\n/-! Legacy import carrier for shared Physics and its model embedding. -/\n\n'
            + 'deprecated_module ' + json.dumps(message)
            + ' (since := ' + json.dumps(migration) + ')\n')
