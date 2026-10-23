"""Exact source/import manifests for separately verified additive topics."""
import hashlib
import json
from pathlib import Path, PurePosixPath


def reviewed_additions(root, topic, known_paths):
    record = json.loads((Path(root)/'docs/topics'/topic/'source-additions.json').read_text())
    if record.get('kind') != topic or not record.get('sources'):
        raise ValueError('Wrong or empty additive-topic manifest')
    sources = record['sources']
    expected = {}
    for file, checksum in sources.items():
        path = PurePosixPath(file)
        if (path.is_absolute() or '..' in path.parts or str(path) != file
                or path.suffix != '.lean' or len(path.parts) < 2
                or path.parts[0] not in ['Math', 'Physics', 'GUT']):
            raise ValueError(f'Invalid added source path: {file}')
        if file in known_paths:
            raise ValueError(f'Addition would replace an existing source: {file}')
        if hashlib.sha256((Path(root)/file).read_bytes()).hexdigest() != checksum:
            raise ValueError(f'Added source checksum changed: {file}')
        aggregate = path.parts[0]+'.lean'
        expected.setdefault(aggregate, []).append('import '+file[:-5].replace('/', '.'))
    imports = record.get('imports', {})
    if (set(imports) != set(expected)
            or any(sorted(imports[a]) != sorted(expected[a]) for a in expected)):
        raise ValueError('Added aggregate imports do not match the exact owned sources')
    return sources, imports
