#!/usr/bin/env python3
"""Compare both remaining-family closures with retained actual compiler measurements.

Does not weaken the full-project exporter. The before state is the completed full-project source-compilation audit. Only
its exact requested closure is selected. The candidate must pass the current
profiler check; ordinary project artifact replay is never a baseline measurement.
"""
import argparse
import csv
import importlib.util
import json
import re
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('profile', Path(__file__).with_name('profile-project.py'))
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--before', type=Path, required=True)
parser.add_argument('--after', type=Path)
parser.add_argument('--baseline-only', action='store_true')
parser.add_argument('--output-dir', type=Path, required=True)
args = parser.parse_args()
targets = sorted('Math.Algebra.HiggsFourWaveCubature.R'+str(r)+'M'+str(m)
                 for r in [0,2] for m in range(35))
if not args.baseline_only:
    if args.after is None:
        parser.error('--after is required unless --baseline-only is selected')
    command = [sys.executable, str(Path(__file__).with_name('profile-project.py')),
               '--work-dir', str(args.after), '--resume', '--check']
    for target in targets:
        command += ['--only', target]
    subprocess.run(command, check=True)


def load(work, historical=False):
    state = json.loads((work/'state.json').read_text())
    graph = {m: s['imports'] for m, s in state['sources'].items()}
    selected = profile.dependency_order(graph, targets)
    if (not set(selected).issubset(state['records']) or
            (not historical and set(selected) != set(state['records']))):
        raise ValueError('Measured records differ from the exact requested closure')
    events = [json.loads(line) for line in (work/'events.jsonl').read_text().splitlines()]
    events = [e for e in events if e['module'] in selected
              and e['fingerprint'] == state['records'][e['module']]['fingerprint']]
    if len(events) != len(selected) or {e['module'] for e in events} != set(selected):
        raise ValueError('Each source needs exactly one fresh successful compiler event')
    fingerprints = {}
    for module in selected:
        inputs = dict(source=state['sources'][module], setup=state['setups'][module],
            dependencies={d:fingerprints[d] for d in graph[module] if d in graph})
        fingerprints[module] = profile.digest(json.dumps(inputs,sort_keys=True).encode())
        setup = work/'artifacts/ir'/profile.module_file(module).with_suffix('.setup.json')
        if profile.digest(setup.read_bytes()) != state['setups'][module]:
            raise ValueError('Setup snapshot drift: '+module)
        row = state['records'][module]
        if not profile.succeeded(row) or row['status'] != 'success' or row['review']:
            raise ValueError('Unresolved compilation or resource-review failure: '+module)
        source = work/'sources'/profile.module_file(module)
        if (profile.digest(source.read_bytes()) != row['sourceSHA256']
                or row['sourceSHA256'] != state['sources'][module]['sha256']
                or row['fingerprint'] != fingerprints[module]):
            raise ValueError('Source snapshot drift: '+module)
        for file, checksum in row['artifacts'].items():
            if profile.digest((work/file).read_bytes()) != checksum:
                raise ValueError('Artifact drift: '+module)
        metadata = work/'artifacts/lib/lean'/profile.module_file(module).with_suffix('.ilean')
        profile.check_project_imports(json.loads(metadata.read_text()),module,graph)
        log = work/row['log']
        if profile.has_errors(log):
            raise ValueError('Compiler logged an error: '+module)
        dependencies = {d: state['records'][d]['artifacts'] for d in graph[module] if d in graph}
        if dependencies != row['dependencyArtifacts']:
            raise ValueError('Dependency drift: '+module)
        event = next(e for e in events if e['module'] == module)
        if event['action'] != 'fresh-compile' or event['fingerprint'] != row['fingerprint']:
            raise ValueError('Event drift: '+module)
    state['records'] = {m:state['records'][m] for m in selected}
    return state


before = load(args.before, historical=True)
frozen = json.loads((ROOT/'docs/topics/higgs-cubature-structure/remaining-frozen-sources.json').read_text())
assert len(frozen) == 70
for target in targets:
    if before['sources'][target]['sha256'] != frozen[str(profile.module_file(target))]:
        raise ValueError('Historical measurement disagrees with frozen source: '+target)
for file, checksum in before['protocol']['pins'].items():
    if profile.digest((ROOT/file).read_bytes()) != checksum:
        raise ValueError('Compiler/dependency pin changed: '+file)

if not args.baseline_only:
    after = load(args.after)
    if before['protocol'] != after['protocol']:
        raise ValueError('Compiler protocols/pins differ')
    old, new = set(before['records']), set(after['records'])
    # Actual imports were checked against this graph while loading each row.
    # A structural proof cannot acquire an old fixed-wave moment premise.
    candidate_graph = {m:row['imports'] for m,row in after['sources'].items()}
    for name in ['TransverseMoments','SecondCollinear']:
        root = 'Math.Algebra.HiggsFourWaveCubature.Structural.'+name
        proof_closure = profile.dependency_order(candidate_graph,[root])
        forbidden = [m for m in proof_closure if re.fullmatch(
            r'Math\.Algebra\.HiggsFourWaveCubature\.R[012]M[0-9]+',m)]
        if forbidden:
            raise ValueError('Structural proof imports old fixed-wave moments: '+str(forbidden))
    additions = {}
    for filename in ['source-additions.json','remaining-source-additions.json']:
        additions.update(json.loads((ROOT/'docs/topics/higgs-cubature-structure'/filename).read_text())['sources'])
    expected_new = {f[:-5].replace('/', '.') for f in additions
                    if not f.endswith(('/Audit.lean','/RemainingAudit.lean'))}
    if old-new or new-old != expected_new or len(old) != 82:
        raise ValueError('Unexpected family closure change')
    for module in old-set(targets):
        if before['sources'][module]['sha256'] != after['sources'][module]['sha256']:
            raise ValueError('Shared source changed: '+module)


def summarize(rows):
    return dict(modules=len(rows), seconds=round(sum(r['seconds'] for r in rows.values()),3),
                peakResidentKiB=max(r['peakResidentKiB'] for r in rows.values()),
                sampledPeakVirtualKiB=max(r['sampledPeakVirtualKiB'] for r in rows.values()))


args.output_dir.mkdir(parents=True,exist_ok=True)
fields = ['module','sourceSHA256','fingerprint','seconds','peakResidentKiB','sampledPeakVirtualKiB','exit']
summary = dict(scope='Transverse and second-collinear families: the same 70 entry modules and complete local dependency closures',
    ordinaryProjectArtifactsReused=0, externalPinnedArtifactsReused=True, protocol=before['protocol'],
    fingerprintScope='Run-specific source/setup/dependency fingerprints; not cross-checkout identities',
    residentMeasurement='OS wait4 maximum RSS', virtualMeasurement='Sampled Linux VmPeak; virtual address space, not RAM')
summary['baselineProvenance'] = 'Selected exact historical compiler invocations from the complete proof-memory audit; not a new baseline run'
summary['comparisonLimit'] = 'Different recorded runs; observational timing comparison with pinned protocols, not controlled simultaneous benchmarking'
states = [('before',before)] if args.baseline_only else [('before',before),('after',after)]
for label,state in states:
    rows=state['records']
    with (args.output_dir/('remaining-'+label+'-measurements.csv')).open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=fields,lineterminator='\n');writer.writeheader()
        for module,row in sorted(rows.items()):
            writer.writerow(dict(module=module,**{f:row[f] for f in fields[1:]}))
    summary[label]=dict(closure=summarize(rows),entryModules=summarize({m:rows[m] for m in targets}),
        freshCompilerEvents=len(rows),failedEvents=0)
if args.baseline_only:
    (args.output_dir/'remaining-baseline-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary['before'],indent=2))
else:
    summary['addedStructuralDependencies']=sorted(new-old)
    summary['compilerTimeReductionPercent']=round(100*(1-summary['after']['closure']['seconds']/summary['before']['closure']['seconds']),1)
    (args.output_dir/'remaining-measurement-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:summary[k] for k in ['before','after','compilerTimeReductionPercent']},indent=2))
