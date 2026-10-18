#!/usr/bin/env python3
"""Check portable documentation metadata; no Git history is required.

Explicitly listed source metadata are exceptions. External revisions and
content checksums are not local work metadata. Numerical measurements are not Git IDs.
"""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
POLICY = Path(__file__).with_name('work-metadata-exceptions.json')


def main():
    policy = json.loads(POLICY.read_text())
    revisions = set(policy['external_revisions'].values())
    files = [ROOT / 'AGENTS.md', ROOT / 'README.md']
    files += [p for p in (ROOT / 'docs').rglob('*')
              if p.suffix in {'.md', '.json'} and p.is_file()]
    errors = []
    checked = 0
    for path in files:
        checked += 1
        rel = path.relative_to(ROOT).as_posix()
        if re.search(r'20\d{2}-\d{2}-\d{2}', path.name):
            errors.append(f'{rel}: dated document filename')
        dates = set(policy['publication_dates'].get(rel, []))
        for number, line in enumerate(path.read_text().splitlines(), 1):
            # External citations and their immutable revisions remain valid.
            line = re.sub(r'\]\([^)]*\)', '](TARGET)', line)
            line = re.sub(r'https?://\S+', 'URL', line)
            for date in re.findall(r'\b20\d{2}-\d{2}-\d{2}\b', line):
                if date not in dates:
                    errors.append(f'{rel}:{number}: work-date candidate {date}')
            for token in re.findall(r'\b[0-9a-f]{7,40}\b', line):
                # Pure numerical ranks, counts and memory measurements are legitimate.
                if token not in revisions and re.search('[a-f]', token) and re.search('[0-9]', token):
                    errors.append(f'{rel}:{number}: local revision candidate {token}')
            if re.search(r'(?:commit|merged as|checkpoint)\s*:?\s*`?\d{7,40}\b', line, re.I):
                errors.append(f'{rel}:{number}: numeric local revision candidate')
            if re.search(r'^- Base(?: commit)?:', line, re.I):
                errors.append(f'{rel}:{number}: retired base metadata field')
            if path.suffix == '.json' and re.search(r'"(?:date|timestamp|base_commit|source_commit)"\s*:', line):
                errors.append(f'{rel}:{number}: retired work metadata key')
    if errors:
        raise SystemExit('\n'.join(errors))
    print(f'PASS: {checked} portable documents/evidence files; '
          'no work-history exemptions; source metadata retained')


if __name__ == '__main__':
    main()
