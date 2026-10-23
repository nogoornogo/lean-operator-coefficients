#!/usr/bin/env python3
"""Export portable measurements only after the full current-project check passes."""
import argparse
import csv
import json
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--work-dir', type=Path, required=True)
parser.add_argument('--output-dir', type=Path, required=True)
args = parser.parse_args()
subprocess.run([sys.executable, str(Path(__file__).with_name('profile-project.py')),
                '--work-dir', str(args.work_dir), '--resume', '--check'], check=True)
state = json.loads((args.work_dir/'state.json').read_text())
rows = state['records']
sources = state['sources']
if set(rows) != set(sources) or any(r['status'] != 'success' or r['review'] for r in rows.values()):
    raise SystemExit('Export requires complete successful coverage with no unresolved review threshold')
args.output_dir.mkdir(parents=True, exist_ok=True)
fields = ['module', 'sourceSHA256', 'fingerprint', 'status', 'seconds',
          'peakResidentKiB', 'sampledPeakVirtualKiB', 'sampledPeakOSThreads', 'exit']
with (args.output_dir/'module-measurements.csv').open('w', newline='') as stream:
    writer = csv.DictWriter(stream, fieldnames=fields, lineterminator='\n')
    writer.writeheader()
    for module, row in sorted(rows.items()):
        writer.writerow({'module': module, **{f: row[f] for f in fields[1:]}})


def maximum(field):
    module = max(rows, key=lambda m: rows[m][field])
    return dict(module=module, value=rows[module][field])


summary = dict(
    scope='Every registered root-project source; external pinned package/toolchain artifacts reused',
    protocol=state['protocol'],
    fingerprintScope='Run-specific source/setup/dependency fingerprint; not a cross-checkout artifact identity',
    measurementScope='One measured successful actual compiler invocation per current source/dependency fingerprint',
    residentMeasurement='OS wait4 maximum RSS',
    virtualMeasurement='Sampled Linux process VmPeak; not physical RAM consumption',
    modules=len(rows), statuses={'success': len(rows), 'failed': 0, 'blocked': 0},
    unresolvedReviewThresholds=0,
    maximumResidentKiB=maximum('peakResidentKiB'),
    maximumVirtualKiB=maximum('sampledPeakVirtualKiB'),
    maximumCompilerSeconds=maximum('seconds'),
    totalCurrentCompilerSeconds=round(sum(r['seconds'] for r in rows.values()), 3))
(args.output_dir/'measurement-summary.json').write_text(json.dumps(summary, indent=2)+'\n')
print(f'Exported {len(rows)} measured source compilations')
