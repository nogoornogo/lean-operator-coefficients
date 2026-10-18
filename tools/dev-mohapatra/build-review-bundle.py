#!/usr/bin/env python3
"""Package the selected review snapshot, without dependencies or third-party papers."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
OUTPUT = Path('/tmp/dev-mohapatra-review.zip')
TOPIC = Path('docs/topics/dev-mohapatra-coefficient-connection')


def collect():
    files = set()
    for directory, pattern in [
        (TOPIC, '*.md'),
        (Path('docs/model-studies/dev-mohapatra'), '*.md'),
        (Path('tools/dev-mohapatra'), '*.py'),
    ]:
        files.update(p.relative_to(ROOT) for p in (ROOT / directory).glob(pattern))
    files.update(Path(p) for p in [
        'docs/proof/current/applications/Physics/DEV_MOHAPATRA_CONNECTION.md',
        'docs/architecture/WORKFLOW.md', 'docs/architecture/MODULE_LAYOUT.md',
        'lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
    ])
    pending = list((ROOT / 'Physics/StandardModel/Operators').glob('DevMohapatra*.lean'))
    pending += list((ROOT / 'Physics/StandardModel/Operators/Audit').glob('AuditDevMohapatra*.lean'))
    while pending:
        path = pending.pop()
        relative = path.relative_to(ROOT)
        if relative in files:
            continue
        files.add(relative)
        for module in re.findall(r'^import\s+([\w.]+)', path.read_text(), re.MULTILINE):
            dependency = ROOT / (module.replace('.', '/') + '.lean')
            if dependency.is_file():
                pending.append(dependency)
    for relative in files:
        if not (ROOT / relative).is_file():
            raise FileNotFoundError(relative)
    return sorted(files)


def main():
    files = collect()
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    manifest = {
        'baseline_commit': revision,
        'note': 'Snapshot includes current working-tree review documents; hashes identify exact contents.',
        'files': {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in files},
    }
    with zipfile.ZipFile(OUTPUT, 'w', zipfile.ZIP_DEFLATED) as archive:
        for relative in files:
            archive.write(ROOT / relative, str(relative))
        archive.writestr('REVIEW_MANIFEST.json', json.dumps(manifest, indent=2) + '\n')
        archive.writestr('START_HERE.txt',
            'Read docs/topics/dev-mohapatra-coefficient-connection/review-guide.md first.\n'
            'This is a selected review snapshot, not a standalone Lean checkout.\n')
    with zipfile.ZipFile(OUTPUT) as archive:
        if archive.testzip() is not None:
            raise RuntimeError('Archive integrity check failed')
        for relative, digest in manifest['files'].items():
            if hashlib.sha256(archive.read(relative)).hexdigest() != digest:
                raise RuntimeError(f'Manifest mismatch: {relative}')
    print(f'{OUTPUT}: {len(files)} files plus manifest and start guide; integrity verified')
    print(f'archive SHA-256: {hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}')


if __name__ == '__main__':
    main()
