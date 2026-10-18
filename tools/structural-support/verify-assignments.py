#!/usr/bin/env python3
"""Opt-in verification target for the retained 572-assignment certificates.

Run from any directory with --output /tmp/NEW-DIRECTORY. Refuses to overwrite
artifacts, refresh expected data, or accept a run without the final strict audit.
The default lake build does not run this target. Uses only the Python stdlib.
"""
import argparse
import collections
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    record = {'status': 'failed', 'rss_guard_gib': 10, 'min_available_gib': 4,
              'timeout_seconds': 300, 'lean_threads': 1, 'runs': []}
    env = dict(os.environ, LEAN_NUM_THREADS='1')

    def run_guard(label, target, build=False):
        command = [sys.executable, str(ROOT/'tools/exact-rank/kernel-probe.py')]
        if build:
            command += ['--build']
        command += [target, str(output/(label+'.log')), '--rss-limit-gib', '10',
                    '--min-available-gib', '4', '--timeout-seconds', '300']
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
        (output/(label+'-guard.log')).write_text(result.stdout+result.stderr)
        match = re.search(r'exit=(-?\d+) elapsed=([\d.]+)s observed_group_peak_kb=(\d+)', result.stdout)
        measurement = {'label': label, 'returncode': result.returncode}
        if match:
            measurement.update(exit=int(match[1]), elapsed_seconds=float(match[2]),
                               sampled_group_peak_kib=int(match[3]))
        record['runs'].append(measurement)
        print(f'{label}: {result.stdout.strip()}', flush=True)
        if result.returncode or not match:
            raise RuntimeError(f'{label} failed; inspect {output}')

    try:
        for renderer, module in [
                ('finite-charge-witnesses.py', 'SMLeptonChargeWitnesses')]:
            rendered = subprocess.check_output([sys.executable, str(HERE/renderer)], cwd=ROOT)
            committed = ROOT/'Physics/StandardModel/Operators'/(module+'.lean')
            if rendered != committed.read_bytes():
                raise RuntimeError(f'{module} differs from its retained renderer; review explicitly')
        run_guard('finite-support-audit',
                  'Physics.StandardModel.Operators.Audit.AuditSMFiniteLeptonSupport', build=True)
        run_guard('minimum-degree-audit',
                  'Physics.StandardModel.Operators.Audit.AuditSMFiniteLeptonDegreeBounds', build=True)
        subprocess.run([sys.executable, str(HERE/'export-assignments.py'), '--output',
                        str(output/'lean-export'), '--compare',
                        str(HERE/'results/assignment-verdicts.csv')], cwd=ROOT, check=True)
        record['lean_export'] = json.loads((output/'lean-export/export.json').read_text())
        expected = json.loads((HERE/'results/assignment-summary.json').read_text())
        for path, wanted in expected['file_sha256'].items():
            if digest((ROOT/path).read_bytes()) != wanted:
                raise RuntimeError(f'retained input identity changed: {path}; review explicitly')
        generator = [sys.executable, str(HERE/'assignment-certificates.py')]
        source = subprocess.check_output(generator, cwd=ROOT)
        table = subprocess.check_output(generator+['--csv'], cwd=ROOT)
        (output/'certificates.lean').write_bytes(source)
        (output/'verdicts.csv').write_bytes(table)
        record['generated_lean_sha256'] = digest(source)
        if digest(source) != expected['generated_lean_sha256']:
            raise RuntimeError('generated source identity changed; review explicitly')
        if table != (HERE/'results/assignment-verdicts.csv').read_bytes():
            raise RuntimeError('regenerated table differs from the retained table')
        rows = list(csv.DictReader(table.decode().splitlines()))
        if len(rows) != expected['assignments']:
            raise RuntimeError('wrong assignment count')
        distributions = {}
        for key in ['b1', 'b2']:
            counts = collections.Counter(abs(int(r[key+'_witness_L'])) for r in rows
                                         if r[key+'_witness_L'] != '')
            distributions[key] = dict(sorted(counts.items()))
        record['absolute_lepton_distributions'] = distributions
        # Build the exact import union before kernel-checking the fresh file.
        imports = sorted(module for module in
                         set(re.findall(r'^import ([A-Za-z0-9_.]+)$', source.decode(), re.M))
                         if (ROOT/(module.replace('.', '/')+'.lean')).is_file())
        for index, module in enumerate(imports):
            run_guard(f'import-{index}', module, build=True)
        run_guard('certificates', str(output/'certificates.lean'))
        log = (output/'certificates.log').read_text()
        audit = re.findall(r'572 assignment certificates: (\d+) strict transitive checks passed', log)
        if audit != [str(expected['strict_transitive_local_checks'])]:
            raise RuntimeError('missing or unexpected final strict transitive audit')
        if re.search(r'\b(?:warning|error):', log):
            raise RuntimeError('certificate emitted warnings/errors')
        degree_source = subprocess.check_output(
            [sys.executable, str(HERE/'degree-certificates.py')], cwd=ROOT)
        (output/'degree-certificates.lean').write_bytes(degree_source)
        record['degree_generated_lean_sha256'] = digest(degree_source)
        run_guard('degree-import', 'Physics.StandardModel.Operators.SMChargeDegreeBounds', build=True)
        run_guard('degree-certificates', str(output/'degree-certificates.lean'))
        degree_log = (output/'degree-certificates.log').read_text()
        degree_audit = re.findall(r'796 degree bounds: (\d+) strict transitive checks passed', degree_log)
        if len(degree_audit) != 1 or int(degree_audit[0]) < 1592:
            raise RuntimeError('missing degree-bound strict transitive audit')
        if re.search(r'\b(?:warning|error):', degree_log):
            raise RuntimeError('degree certificate emitted warnings/errors')
        record.update(degree_bounds=796, degree_strict_transitive_checks=int(degree_audit[0]))
        record.update(status='kernel_verified', assignments=len(rows),
                      strict_transitive_local_checks=int(audit[0]))
        print('PASS: retained source/table identities, 572 assignments and final strict audit', flush=True)
        return 0
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        record['failure'] = str(error)
        print(str(error), file=sys.stderr)
        return 1
    finally:
        (output/'verification.json').write_text(json.dumps(record, indent=2)+'\n')


if __name__ == '__main__':
    sys.exit(main())
