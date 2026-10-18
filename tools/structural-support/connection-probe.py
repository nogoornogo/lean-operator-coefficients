#!/usr/bin/env python3
"""Reproduce the earlier stopped projection check with persistent progress.

Generated diagnostic only, never a theorem premise. This intentionally retains
an expensive OLD connection; do not substitute it for the verified new module.
Run serially under kernel-probe.py with 10 GiB/120 s and a 4 GiB host reserve.
"""
import argparse
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def generate(progress, imports_only=False):
    source = (HERE/'probes/sm-joint-support-data-candidate.lean.txt').read_text()
    imports = '\n'.join(s for s in source.splitlines() if s.startswith('import '))

    def marker(name):
        return f'run_cmd do IO.FS.writeFile {json.dumps(str(progress))} {json.dumps(name)}\n\n'

    if imports_only:
        return imports+'\n'+marker('IMPORTS_READY')
    source = source[:source.index('abbrev Index')]
    source = source.replace('/-- Direct syntax dispatch; no projection from a representation or its proof. -/', '')
    source = re.sub(r'^(def|theorem) (\w+)', lambda m: marker('BEGIN '+m[2])+m[0], source, flags=re.M)
    return source+marker('END coreData_eq')+'end GUT.SMJointSupportData\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--progress', type=Path, required=True, help='one explicit /tmp progress file')
    parser.add_argument('--imports-only', action='store_true')
    args = parser.parse_args()
    if args.progress.parent != Path('/tmp'):
        parser.error('use an explicit file directly inside /tmp')
    print(generate(args.progress, args.imports_only), end='')
