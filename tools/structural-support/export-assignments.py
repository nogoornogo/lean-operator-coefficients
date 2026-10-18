#!/usr/bin/env python3
"""Export the Lean-owned assignment domain/verdicts to an optional CSV.

Build SMFiniteLeptonDegreeBounds first. No input CSV is needed. --compare is
an optional external regression check and never a Lean theorem premise.
"""
import argparse
import csv
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--compare', type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = output/'export.lean'
    source.write_bytes((HERE/'probes/export-assignments.lean.txt').read_bytes())
    record = {'status': 'failed', 'csv_is_proof_input': False}
    try:
        command = [sys.executable, str(ROOT/'tools/exact-rank/kernel-probe.py'),
                   str(source), str(output/'export.log'), '--rss-limit-gib', '10',
                   '--min-available-gib', '4', '--timeout-seconds', '300',
                   '--require-cached', 'Physics.StandardModel.Operators.SMFiniteLeptonDegreeBounds']
        result = subprocess.run(command, cwd=ROOT, env=dict(os.environ, LEAN_NUM_THREADS='1'),
                                capture_output=True, text=True)
        (output/'guard.log').write_text(result.stdout+result.stderr)
        match = re.search(r'exit=(-?\d+) elapsed=([\d.]+)s observed_group_peak_kb=(\d+)', result.stdout)
        if match:
            record.update(elapsed_seconds=float(match[2]), sampled_group_peak_kib=int(match[3]))
        if result.returncode or not match:
            raise RuntimeError(f'Lean export failed; inspect {output}')
        log = (output/'export.log').read_text()
        if re.search(r'\b(?:warning|error):', log):
            raise RuntimeError('Lean export emitted warnings/errors')
        header = 'k,q,l,b1_forbidden,b1_witness_L,b2_forbidden,b2_witness_L,b1_forbidden_b2_allowed\n'
        start = log.find(header)
        if start < 0:
            raise RuntimeError('Lean export did not emit the expected header')
        table = log[start:].encode()
        rows = list(csv.DictReader(io.StringIO(table.decode())))
        if len(rows) != 572 or set(rows[0]) != {
                'k','q','l','b1_forbidden','b1_witness_L','b2_forbidden','b2_witness_L',
                'b1_forbidden_b2_allowed'}:
            raise RuntimeError('unexpected export diagnostics/header/row count')
        (output/'assignments.csv').write_bytes(table)
        if args.compare and table != args.compare.read_bytes():
            raise RuntimeError('Lean export differs from the selected external CSV')
        record.update(status='exported', rows=len(rows), compared=bool(args.compare))
        print(result.stdout.strip(), flush=True)
        print(f'Lean-owned CSV exported to {output / "assignments.csv"}', flush=True)
        return 0
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        record['failure'] = str(error)
        print(error, file=sys.stderr)
        return 1
    finally:
        (output/'export.json').write_text(json.dumps(record, indent=2)+'\n')


if __name__ == '__main__':
    sys.exit(main())
