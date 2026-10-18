#!/usr/bin/env python3
"""Serial structural kernel comparison of all 107 neutral keys and remaining probes.

CSV multiplicities only propose statements. A Lean failure is unknown or mismatch,
never a theorem premise or inferred false value. Uses the existing guarded runner.
"""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
KEYS = ('species', 'fermions', 'm', 'delta')
FIELDS = ['case', *KEYS, 'expected_support', 'outcome', 'elapsed_seconds',
          'peak_group_kib', 'lean_exit', 'detail']
BASE = '''import Physics.StandardModel.Operators.SMCompactSupportDecision
import Lean.Util.CollectAxioms
open Math GUT
attribute [local instance] SMCompactSupportDecision.contentDecision
attribute [local instance] SMCompactSupportDecision.higgsDecision
'''
AUDIT = '''
run_cmd do
  for ax in (← Lean.collectAxioms ``candidate) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "candidate uses unexpected axiom {ax}"
  Lean.logInfo "candidate strict transitive audit passed"
'''


def key(row):
    return tuple(int(row[k]) for k in KEYS)


def domain():
    reference = ROOT / 'tools/exact-rank/neutral-sparse-results.csv'
    original = ROOT / 'tools/exact-rank/constant-content-ranks.csv'
    with reference.open() as f:
        rows = list(csv.DictReader(f))
    with original.open() as f:
        old = [r for r in csv.DictReader(f) if r['status'] == 'unclassified']
    keys = [key(r) for r in rows]
    old_keys = [key(r) for r in old]
    if (len(rows) != 107 or len(set(keys)) != 107 or len(old_keys) != 107
            or len(set(old_keys)) != 107 or set(keys) != set(old_keys)):
        raise ValueError('107-row input domain mismatch/duplicate')
    old_columns = {key(r): int(r['columns']) for r in old}
    # Pinned actual signed field dictionary, matching DeltaLOneSignedInput.
    hypercharges = [1, 4, -2, -3, -6, -1, -4, 2, 3, 6]
    for r in rows:
        s, n, m, delta = key(r)
        if not (0 <= s < 10 and n > 0 and m >= abs(delta) and (m-delta) % 2 == 0
                and n*hypercharges[s]+3*delta == 0
                and 0 <= int(r['multiplicity']) <= int(r['columns'])
                and int(r['columns']) == old_columns[key(r)]
                and int(r['rank']) == int(r['columns'])-int(r['multiplicity'])):
            raise ValueError(f'invalid reference conventions: {key(r)}')
    return rows, {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in [reference, original]}


def cases(rows):
    for name, proposition in [
        ('compiled-positive', 'SMJointHiggsSupport.HiggsSupport (fun _ : Fin 2 => 3) 2 0'),
        ('compiled-negative', 'SMJointHiggsSupport.HiggsSupport (fun _ : Fin 2 => 4) 4 0'),
    ]:
        yield name, {}, '', BASE + '#eval decide (' + proposition + ')\n'
    # Actual neutral original-space mixed source with odd conjugate-Q spin count.
    mixed = '''theorem candidate : SelectionCriteria.Forbidden
    (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (0 : ZMod 1) 0)
      (fun i : Fin 21 => if i.val < 18 then 0 else 5) 0 5) := by
  apply (SMJointHiggsSupport.original_ql_forbidden_iff _ (0 : ZMod 1) 0 0 5).mpr
  apply Or.inr
  apply Or.inr
  decide +kernel
'''
    yield 'mixed-Q18-conjugateQ3', {}, 'false', BASE + mixed + AUDIT
    for r in rows:
        s, n, m, delta = key(r)
        expected = int(r['multiplicity']) > 0
        prop = f'SMJointContentSupport.Supports (fun t => if t = {s} then {n} else 0) {m}'
        claim = prop if expected else '¬ (' + prop + ')'
        source = BASE + 'theorem candidate : ' + claim + ' := by decide +kernel\n' + AUDIT
        yield f'neutral-{s}-{n}-{m}-{delta}', r, str(expected).lower(), source


def classify(code, output, log, compiled):
    if code == 0:
        if compiled:
            return 'compiled', 'closed compiled evaluation succeeded'
        if 'candidate strict transitive audit passed' not in log:
            return 'diagnostic_error', 'missing strict audit confirmation'
        return 'matched', 'kernel statement and strict transitive audit passed'
    if 'host available-memory reserve' in output or 'below the requested reserve' in output:
        return 'unknown_host_memory', 'host reserve interrupted/refused; batch stops'
    if 'group RSS limit' in output:
        return 'unknown_memory', '10 GiB sampled group RSS guard interrupted'
    if 'wall-clock limit' in output:
        return 'unknown_timeout', '300-second per-case guard interrupted'
    if 'deep recursion' in log or 'maximum recursion depth' in log:
        return 'unknown_recursion', 'unchanged Lean recursion limit'
    if 'maximum number of heartbeats' in log or 'deterministic timeout' in log:
        return 'unknown_heartbeats', 'unchanged Lean heartbeat limit'
    if compiled and 'dependsOnNoncomputable' in log:
        return 'unsupported_compiled', 'noncomputable decision dependency'
    if 'Tactic `decide` proved that the proposition' in log and 'is false' in log:
        return 'mismatch', 'Lean rejected the proposed reference sign as false'
    return 'diagnostic_error', log[-1200:].replace('\n', ' ')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--metadata', required=True, type=Path)
    parser.add_argument('--logs', required=True, type=Path)
    args = parser.parse_args()
    rows, hashes = domain()
    args.logs.mkdir(parents=True, exist_ok=False)
    records = []
    interrupted = False
    try:
        with args.output.open('w', newline='') as target:
            writer = csv.DictWriter(target, fieldnames=FIELDS, lineterminator="\n")
            writer.writeheader()
            for name, r, expected, source in cases(rows):
                path = args.logs / (name + '.lean')
                logpath = args.logs / (name + '.log')
                path.write_text(source)
                command = [sys.executable, str(ROOT/'tools/exact-rank/kernel-probe.py'),
                           '--rss-limit-gib', '10', '--min-available-gib', '4',
                           '--timeout-seconds', '300', str(path), str(logpath)]
                result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                        env={**os.environ, 'LEAN_NUM_THREADS': '1'})
                output = result.stdout + result.stderr
                (args.logs/(name + '.runner.log')).write_text(output)
                log = logpath.read_text() if logpath.exists() else ''
                outcome, detail = classify(result.returncode, output, log, name.startswith('compiled-'))
                metrics = re.search(r'exit=(-?\d+) elapsed=([\d.]+)s observed_group_peak_kb=(\d+)', output)
                record = {'case': name, **{k: r.get(k, '') for k in KEYS},
                          'expected_support': expected, 'outcome': outcome,
                          'elapsed_seconds': metrics[2] if metrics else '',
                          'peak_group_kib': metrics[3] if metrics else '',
                          'lean_exit': metrics[1] if metrics else '', 'detail': detail}
                records.append(record)
                writer.writerow(record)
                target.flush()
                print(json.dumps(record), flush=True)
                if outcome in ('unknown_host_memory', 'mismatch', 'diagnostic_error'):
                    print('Stopping batch for investigation; unattempted keys remain unverified.', flush=True)
                    break
    except KeyboardInterrupt:
        interrupted = True
        print('Interrupted: pending case is not accepted; completed records are preserved.', flush=True)
    finally:
        args.metadata.write_text(json.dumps({'input_sha256': hashes, 'reference_rows': len(rows),
            'reference_positive': sum(int(r['multiplicity']) > 0 for r in rows),
            'reference_zero': sum(int(r['multiplicity']) == 0 for r in rows),
            'completed_cases': len(records), 'complete': len(records) == len(rows)+3,
            'interrupted': interrupted, 'all_checks_passed': len(records) == len(rows)+3 and all(
            r['outcome'] in ('matched', 'compiled') for r in records), 'sampled_rss_limit_gib': 10,
            'host_reserve_gib': 4, 'per_case_timeout_seconds': 300,
            'logs': str(args.logs)}, indent=2)+'\n')
    return 130 if interrupted else (0 if len(records) == len(rows)+3 and all(
        r['outcome'] in ('matched', 'compiled') for r in records) else 1)


if __name__ == '__main__':
    sys.exit(main())
