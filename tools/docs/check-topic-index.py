#!/usr/bin/env python3
"""Check complete subject navigation and outcome coverage, without status inference."""
import argparse
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2] / 'docs/topics'


def check(root, pending):
    topics = {p.parent.name for p in root.glob('*/README.md')
              if p.parent.name != '_history'}
    subject = set(re.findall(r'\]\(([^/()]+)/README\.md\)',
                             (root / 'README.md').read_text()))
    subject.discard('_history')  # The guide itself is navigation infrastructure.
    outcomes = set()
    errors = []
    volumes = sorted((root / '_history').glob('*_topics_history.md'))
    if not volumes:
        errors.append('missing outcome volumes')
    for number, volume in enumerate(volumes, 1):
        if volume.name != f'{number:03d}_topics_history.md':
            errors.append(f'nonsequential volume: {volume.name}')
        entries = []
        for line in volume.read_text().splitlines():
            if not line.startswith('- ['):
                continue
            match = re.fullmatch(r'- \[[^\]]+\]\(\.\./([^/()]+)/\): (.+)', line)
            if not match:
                errors.append(f'malformed outcome entry in {volume.name}')
                continue
            entries.append(match.group(1))
        if not 1 <= len(entries) <= 30:
            errors.append(f'invalid entry count in {volume.name}: {len(entries)}')
        outcomes.update(entries)
    for label, names in (
            ('missing subject links', topics - subject),
            ('unknown subject targets', subject - topics),
            ('missing outcome links', topics - outcomes - pending),
            ('unknown outcome targets', outcomes - topics),
            ('unknown pending topics', pending - topics)):
        if names:
            errors.append(f'{label}: {", ".join(sorted(names))}')
    if errors:
        raise ValueError('\n'.join(errors))
    return len(topics), len(outcomes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pending-topic', action='append', default=[],
                        help='explicit pending integration/outcome exception; repeatable')
    args = parser.parse_args()
    pending = set(args.pending_topic)
    try:
        topics, outcomes = check(ROOT, pending)
    except ValueError as error:
        parser.exit(1, f'FAIL: {error}\n')
    print(f'PASS: {topics} topics indexed; {outcomes} topics with outcomes; '
          f'pending exceptions: {", ".join(sorted(pending)) or "none"}')


if __name__ == '__main__':
    main()
