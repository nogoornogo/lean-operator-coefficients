"""Exact, declaration-bounded replay of reviewed proof-body replacements."""
import json
from pathlib import Path
import re

REGISTRY = Path('docs/topics/proof-memory-audit/proof-rewrites.json')
DECLARATION = re.compile(
    r'^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)?'
    r'(?:theorem|lemma|def|abbrev|instance|end|section|namespace)\b', re.M)


def load_rewrites(root=Path('.')):
    path = Path(root)/REGISTRY
    records = json.loads(path.read_text()) if path.exists() else []
    child = Path(root)/'docs/topics/higgs-cubature-structure/proof-rewrites.json'
    return records + (json.loads(child.read_text()) if child.exists() else [])


def fragment_position(source, statement, fragment):
    if source.count(statement) != 1:
        raise ValueError('Declaration statement missing or ambiguous in proof replay')
    start = source.index(statement) + len(statement)
    tail = source[start:]
    end = DECLARATION.search(tail)
    body = tail[:end.start()] if end else tail
    if body.count(fragment) != 1:
        raise ValueError('Proof fragment missing or ambiguous inside its declaration')
    return start + body.index(fragment)


def line_span(source, start, fragment):
    return [source[:start].count('\n'), source[:start+len(fragment)].count('\n')]


def apply_rewrites(source, record):
    if preamble := record.get('preamble'):
        for text in preamble.values():
            if any(line and not line.startswith(('import ', '/-! Exact ordered moments,'))
                   for line in text.splitlines()):
                raise ValueError('Proof replay preamble contains a declaration or option')
        if not source.startswith(preamble['before']):
            raise ValueError('Proof replay preamble differs from the frozen source')
        source = preamble['after'] + source[len(preamble['before']):]
    for change in record['changes']:
        at = fragment_position(source, change['statement'], change['before'])
        source = source[:at] + change['after'] + source[at+len(change['before']):]
    if execution := record.get('execution'):
        # This bounded scheduling change does not alter a proof or resource cap.
        if execution['insertion'] not in (
                '-- Check finite certificates sequentially to avoid blocked elaboration worker stacks.\n'
                'set_option Elab.async false\n\n',
                '-- Elaborate proofs sequentially to avoid blocked worker stacks.\n'
                'set_option Elab.async false\n\n'):
            raise ValueError('Unreviewed execution-option insertion')
        if source.count(execution['marker']) != 1:
            raise ValueError('Execution-option marker missing or ambiguous')
        source = source.replace(execution['marker'], execution['insertion'] + execution['marker'], 1)
    return source


def rewritten_ranges(source, record):
    return [line_span(source, fragment_position(source, c['statement'], c['after']), c['after'])
            for c in record['changes']]


def baseline_ranges(source, record):
    ranges = []
    for change in record['changes']:
        fragment = change.get('baselineBefore', change['before'])
        statement = change.get('baselineStatement', change['statement'])
        actual = line_span(source, fragment_position(source, statement, fragment), fragment)
        if actual != change['baselineProofLines']:
            raise ValueError('Recorded baseline proof range disagrees with frozen source')
        ranges.append(actual)
    return ranges
