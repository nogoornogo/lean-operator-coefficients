#!/usr/bin/env python3
"""Compile project sources into an isolated, measured dependency-ordered build.

Only external package/toolchain artifacts are inherited. Resume reuses outputs
produced and fingerprinted by this audit, never ordinary project build caches.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import signal
import subprocess
import time

GIB = 1024 ** 3
CAP = 16 * GIB
TIMEOUT = 540
REVIEW_RSS_KIB = 6 * 1024 ** 2
REVIEW_VIRTUAL_KIB = 14 * 1024 ** 2


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def module_file(name):
    return Path(name.replace('.', '/') + '.lean')


def project_graph(root):
    code = '''import {collectSources, imports, validate} from './tools/layout/check-layout.mjs';
const sources = collectSources('.');
const errors = validate(sources);
if (errors.length) throw Error(errors.join('\\n'));
process.stdout.write(JSON.stringify(Object.fromEntries(Object.entries(sources).map(
 ([name,text]) => [name,imports(text)]))));'''
    return json.loads(subprocess.check_output(
        ['node', '--input-type=module', '-e', code], cwd=root, text=True))


def dependency_order(graph, requested):
    seen, order = set(), []
    def visit(module):
        if module in seen:
            return
        seen.add(module)
        for dep in graph[module]:
            if dep in graph:
                visit(dep)
        order.append(module)
    for module in requested:
        if module not in graph:
            raise ValueError('Unknown project module: ' + module)
        visit(module)
    return order


def guard():
    resource.setrlimit(resource.RLIMIT_AS, (CAP, CAP))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def measured_compile(command, env, log, cwd, timeout=TIMEOUT):
    peak = {}
    start = time.monotonic()
    timed_out = False
    killed_at = None
    last_progress = 0
    with log.open('w') as output:
        child = subprocess.Popen(command, cwd=cwd, env=env, stdout=output,
                                 stderr=subprocess.STDOUT, start_new_session=True,
                                 preexec_fn=guard)
        while True:
            try:
                status = Path(f'/proc/{child.pid}/status').read_text()
                for line in status.splitlines():
                    key, _, value = line.partition(':')
                    if key in ['VmPeak', 'VmRSS', 'Threads']:
                        peak[key] = max(peak.get(key, 0), int(value.split()[0]))
            except (FileNotFoundError, ProcessLookupError):
                pass
            pid, status, usage = os.wait4(child.pid, os.WNOHANG)
            if pid:
                child.returncode = os.waitstatus_to_exitcode(status)
                break
            elapsed = time.monotonic() - start
            if elapsed - last_progress >= 30:
                print(f'RUNNING {log.stem}: {elapsed:.0f}s; '
                      f'sampled RSS {peak.get("VmRSS", 0)/1024**2:.2f} GiB; '
                      f'virtual {peak.get("VmPeak", 0)/1024**2:.2f} GiB', flush=True)
                last_progress = elapsed
            if elapsed >= timeout and not timed_out:
                timed_out = True
                killed_at = elapsed
                os.killpg(child.pid, signal.SIGTERM)
            elif timed_out and elapsed >= killed_at + 2:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            time.sleep(.1)
    return dict(exit=child.returncode, timeout=timed_out,
                seconds=round(time.monotonic()-start, 3),
                userCPUSeconds=round(usage.ru_utime, 3),
                systemCPUSeconds=round(usage.ru_stime, 3),
                peakResidentKiB=usage.ru_maxrss,
                sampledPeakVirtualKiB=peak.get('VmPeak', 0),
                sampledPeakOSThreads=peak.get('Threads', 0))


def succeeded(row):
    return row['exit'] == 0 and not row['timeout'] and not row.get('reportedErrors', False)


def has_errors(log):
    # Lean/Lake also reject the anomalous case of logged errors with exit zero.
    return any(re.match(r'^(?:.*\.lean:\d+:\d+:\s*)?error:', line)
               for line in log.read_text().splitlines())


def check_project_imports(data, module, graph):
    actual = {entry[0] for entry in data['directImports'] if entry[0] in graph}
    expected = {name for name in graph[module] if name in graph}
    if actual != expected:
        raise ValueError('Compiler/source dependency graph disagreement: '+module)


def relocate_setup(raw, ordinary_build, isolated_build, module, graph):
    text = raw.replace(str(ordinary_build)+'/', str(isolated_build)+'/')
    setup = json.loads(text)
    if setup['name'] != module:
        raise ValueError('Stale setup module: '+module)
    for dep in graph[module]:
        if dep in graph and dep not in setup['importArts']:
            raise ValueError(f'Stale setup misses direct import {module} -> {dep}')
    for name, groups in setup['importArts'].items():
        if name in graph:
            for group in groups:
                if any(not Path(p).is_relative_to(isolated_build/'lib/lean') for p in group):
                    raise ValueError('Inherited project artifact outside the audit: '+name)
    for kind in ['dynlibs', 'plugins']:
        if any(Path(p).is_relative_to(isolated_build) for p in setup.get(kind, [])):
            raise ValueError('Project native plugin needs a separate build: '+module)
    return text


def import_header(source):
    # Preserve line positions while ignoring nested comments. Header commands
    # contain no strings; stop before the first actual non-header command.
    clean, depth, index = [], 0, 0
    while index < len(source):
        pair = source[index:index+2]
        char = source[index]
        if depth:
            if pair == '/-':
                depth += 1
                index += 2
                continue
            if pair == '-/':
                depth -= 1
                index += 2
                continue
            if char == '\n':
                clean.append('\n')
        elif pair == '/-':
            depth = 1
            index += 2
            continue
        elif pair == '--':
            while index < len(source) and source[index] != '\n':
                index += 1
            continue
        else:
            clean.append(char)
        index += 1
    end = 0
    for line_no, line in enumerate(''.join(clean).splitlines(), 1):
        text = line.strip()
        if not text:
            continue
        if text in ['module', 'prelude'] or re.match(r'(?:(?:public|private|meta)\s+)*import\s', text):
            end = line_no
        else:
            break
    return ''.join(source.splitlines(keepends=True)[:end])


def reusable_record(row, fingerprint, outputs, work, dependencies):
    return bool(row and row.get('status') == 'success' and row['fingerprint'] == fingerprint
                and row.get('dependencyArtifacts') == dependencies
                and all(p.exists() and digest(p.read_bytes()) == row['artifacts'].get(str(p.relative_to(work)))
                        for p in outputs))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--only', action='append', default=[], metavar='MODULE',
                        help='Compile this dependency closure; default is the entire project')
    parser.add_argument('--priority', action='append', default=[], metavar='MODULE',
                        help='Compile this closure before the rest of the project')
    parser.add_argument('--imports-only', metavar='MODULE',
                        help='Measure matching imports without the target body; compile dependencies if needed')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--refresh', action='store_true',
                        help='With --resume, update changed sources and invalidate their dependents')
    parser.add_argument('--check', action='store_true',
                        help='Check successful current fingerprints and artifacts without compiling')
    args = parser.parse_args()
    if args.imports_only and (args.only or args.priority or args.check):
        parser.error('--imports-only cannot combine with --only, --priority or --check')
    root = Path.cwd().resolve()
    work = args.work_dir.resolve()
    if work == root or work == root/'.lake/build' or work in root.parents:
        parser.error('Use a separate audit directory, not the ordinary project build')
    if args.refresh and not args.resume:
        parser.error('--refresh requires --resume')
    state_file = work/'state.json'
    if args.check and not state_file.exists():
        parser.error('No measured state exists')
    if work.exists() and any(work.iterdir()) and not args.resume and not args.check:
        parser.error('Nonempty audit directory: use --resume or a new directory')
    if args.resume and not state_file.exists():
        parser.error('No previous audit state exists')
    work.mkdir(parents=True, exist_ok=True)
    lock = (work/'run.lock').open('w')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        parser.error('Another audit is using this directory')

    graph = project_graph(root)
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=root, text=True).strip()
    search = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=root, text=True).strip().split(':')
    ordinary = (root/'.lake/build/lib/lean').resolve()
    search = [p for p in search if Path(p).resolve() != ordinary]
    if any(Path(p).resolve() == ordinary for p in search):
        raise ValueError('Ordinary project artifacts remain in the import search path')
    pins = {f: digest((root/f).read_bytes()) for f in
            ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']}
    protocol = dict(pins=pins, lean=subprocess.check_output([lean, '--version'], text=True).strip(),
                    virtualLimitBytes=CAP, timeoutSeconds=TIMEOUT, leanArguments=['-j2'],
                    coreDumpsEnabled=False, ordinaryProjectCacheInherited=False)
    source_info = {m: dict(file=module_file(m).as_posix(),
                          sha256=digest((root/module_file(m)).read_bytes()),
                          imports=deps) for m, deps in graph.items()}
    if state_file.exists():
        state = json.loads(state_file.read_text())
        if state['project'] != str(root) or state['protocol'] != protocol:
            raise ValueError('Project, toolchain, pins or resource protocol changed')
        if state['sources'] != source_info and (args.check or not args.refresh):
            raise ValueError('Source graph changed: update explicitly with --resume --refresh')
    else:
        state = dict(project=str(root), protocol=protocol, sources={}, setups={}, records={})
    order = dependency_order(graph, [args.imports_only] if args.imports_only else args.only or [*args.priority, 'GUT'])
    prepare_order = order[:]
    if args.imports_only:
        order = order[:-1]
    snapshot = work/'sources'
    build = work/'artifacts'
    lib = build/'lib/lean'
    ir = build/'ir'
    logs = work/'logs'
    for directory in [snapshot, lib, ir, logs]:
        directory.mkdir(parents=True, exist_ok=True)
    if not args.check:
        for m, info in source_info.items():
            if state['sources'].get(m) != info:
                dest = snapshot/info['file']
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes((root/info['file']).read_bytes())
                state['setups'].pop(m, None)
        state['sources'] = source_info
        save(state_file, state)
        # Snapshot Lake's exact package/options/import artifact selection. Only
        # project artifact paths move; external package artifacts stay pinned.
        print(f'PREPARE {len(prepare_order)} modules; inherited project cache: 0', flush=True)
        for i, module in enumerate(prepare_order, 1):
            if module not in state['setups']:
                old = root/'.lake/build/ir'/module_file(module).with_suffix('.setup.json')
                if not old.exists():
                    raise ValueError(f'Missing Lake setup for {module}; build its setup first')
                raw = old.read_text()
                text = relocate_setup(raw, root/'.lake/build', build, module, graph)
                dest = ir/module_file(module).with_suffix('.setup.json')
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text(text)
                state['setups'][module] = digest(text.encode())
            dest = ir/module_file(module).with_suffix('.setup.json')
            if digest(dest.read_bytes()) != state['setups'][module]:
                raise ValueError('Audit setup snapshot was modified: '+module)
            if digest((snapshot/module_file(module)).read_bytes()) != source_info[module]['sha256']:
                raise ValueError('Audit source snapshot was modified: '+module)
            if i % 500 == 0:
                print(f'PREPARE {i}/{len(prepare_order)}', flush=True)
                save(state_file, state)
        save(state_file, state)

    fingerprints = {}
    all_order = dependency_order(graph, ['GUT'])
    for m in all_order:
        inputs = dict(source=source_info[m], setup=state['setups'].get(m),
                      dependencies={d: fingerprints[d] for d in graph[m] if d in graph})
        fingerprints[m] = digest(json.dumps(inputs, sort_keys=True).encode())
    module_kinds = {}
    imports_checked = set()
    def paths(m):
        stem = module_file(m).with_suffix('')
        if m not in module_kinds:
            module_kinds[m] = json.loads((ir/module_file(m).with_suffix('.setup.json')).read_text())['isModule']
        extra = ['.olean.server', '.olean.private', '.ir', '.ir.sig'] if module_kinds[m] else []
        return ([Path(str(lib/stem)+s) for s in ['.olean', '.ilean']]
                + [Path(str(ir/stem)+'.c')] + [Path(str(lib/stem)+s) for s in extra])
    def reusable(m):
        row = state['records'].get(m)
        dependencies = {d: state['records'].get(d, {}).get('artifacts')
                        for d in graph[m] if d in graph}
        outputs = paths(m)
        if not (reusable_record(row, fingerprints[m], outputs, work, dependencies)
                and not has_errors(work/row['log'])):
            return False
        if m not in imports_checked:
            check_project_imports(json.loads(outputs[1].read_text()), m, graph)
            imports_checked.add(m)
        return True
    if args.check:
        for m in order:
            if (digest((snapshot/module_file(m)).read_bytes()) != source_info[m]['sha256']
                    or digest((ir/module_file(m).with_suffix('.setup.json')).read_bytes()) != state['setups'][m]):
                raise ValueError('Audit input snapshot was modified: '+m)
        missing = [m for m in order if not reusable(m)]
        if missing:
            raise SystemExit(f'{len(missing)} modules lack successful current measured artifacts: {missing[:6]}')
        print(f'PASS: {len(order)} current source/dependency fingerprints have measured successful compilations')
        return

    counts = dict(compiled=0, reusedMeasured=0, blocked=0, failed=0, inheritedProjectCache=0)
    paused = False
    env = {**os.environ, 'LEAN_PATH': ':'.join([str(lib), *search]), 'LEAN_NUM_THREADS': '2'}
    for i, module in enumerate(order, 1):
        if (work/'pause-request').exists():
            # Stop between compiler processes, retaining completed measurements.
            paused = True
            print('PAUSED before compiler launch: '+module, flush=True)
            break
        if reusable(module):
            counts['reusedMeasured'] += 1
            continue
        blocked = [d for d in graph[module] if d in graph and not reusable(d)]
        if blocked:
            state['records'][module] = dict(status='blocked', fingerprint=fingerprints[module], dependencies=blocked)
            counts['blocked'] += 1
            if i % 10 == 0:
                save(state_file, state)
            continue
        outputs = paths(module)
        for p in outputs:
            p.parent.mkdir(parents=True, exist_ok=True)
        setup = ir/module_file(module).with_suffix('.setup.json')
        log = logs/module_file(module).with_suffix('.log')
        log.parent.mkdir(parents=True, exist_ok=True)
        command = [lean, '-j2', '-R', str(snapshot), str(snapshot/module_file(module)),
                   '-o', str(outputs[0]), '-i', str(outputs[1]), '-c', str(outputs[2]), '--setup', str(setup)]
        print(f'START {i}/{len(order)} {module}', flush=True)
        row = measured_compile(command, env, log, root)
        row['reportedErrors'] = has_errors(log)
        row.update(fingerprint=fingerprints[module], sourceSHA256=source_info[module]['sha256'],
                   status='success' if succeeded(row) else 'failed',
                   log=str(log.relative_to(work)),
                   dependencyArtifacts={d: state['records'][d]['artifacts'] for d in graph[module] if d in graph})
        row['review'] = (row['status'] != 'success' or row['peakResidentKiB'] >= REVIEW_RSS_KIB
                         or row['sampledPeakVirtualKiB'] >= REVIEW_VIRTUAL_KIB)
        if row['status'] == 'success':
            data = json.loads(outputs[1].read_text())
            if data['module'] != module:
                raise ValueError('Compiled metadata has wrong module: '+module)
            check_project_imports(data, module, graph)
            imports_checked.add(module)
            row['artifacts'] = {str(p.relative_to(work)): digest(p.read_bytes()) for p in outputs}
        else:
            counts['failed'] += 1
        counts['compiled'] += 1
        state['records'][module] = row
        if i % 10 == 0 or row['status'] != 'success':
            save(state_file, state)
        with (work/'events.jsonl').open('a') as events:
            events.write(json.dumps(dict(module=module, action='fresh-compile', command=command, **row))+'\n')
        print(f'END {module}: {row["status"]}; RSS {row["peakResidentKiB"]/1024**2:.2f} GiB; '
              f'virtual {row["sampledPeakVirtualKiB"]/1024**2:.2f} GiB; {row["seconds"]:.1f}s'
              + (' REVIEW' if row['review'] else ''), flush=True)
    if args.imports_only and not paused and not counts['failed'] and not counts['blocked']:
        module = args.imports_only
        control_root = work/'import-controls'
        control = control_root/'sources'/module_file(module)
        control.parent.mkdir(parents=True, exist_ok=True)
        control.write_text(import_header((snapshot/module_file(module)).read_text()))
        out = control_root/'artifacts'/module_file(module).with_suffix('')
        out.parent.mkdir(parents=True, exist_ok=True)
        log = control_root/'logs'/module_file(module).with_suffix('.log')
        log.parent.mkdir(parents=True, exist_ok=True)
        command = [lean, '-j2', '-R', str(control_root/'sources'), str(control),
                   '-o', str(out)+'.olean', '-i', str(out)+'.ilean', '-c', str(out)+'.c',
                   '--setup', str(ir/module_file(module).with_suffix('.setup.json'))]
        row = measured_compile(command, env, log, root)
        row['reportedErrors'] = has_errors(log)
        row.update(fingerprint=fingerprints[module], status='success' if succeeded(row) else 'failed',
                   dependencyArtifacts={d: state['records'][d]['artifacts'] for d in graph[module] if d in graph},
                   log=str(log.relative_to(work)))
        if row['status'] == 'success' and json.loads(Path(str(out)+'.ilean').read_text())['decls']:
            raise ValueError('Import-only control introduced declarations: '+module)
        state.setdefault('importControls', {})[module] = row
        if row['status'] != 'success':
            counts['failed'] += 1
        print(f'IMPORT CONTROL {module}: {row["status"]}; RSS {row["peakResidentKiB"]/1024**2:.2f} GiB; '
              f'virtual {row["sampledPeakVirtualKiB"]/1024**2:.2f} GiB', flush=True)
    summary = dict(scope='import-only control; target proof not compiled' if args.imports_only else
                        'selected dependency closures' if args.only else 'entire project',
                   modules=len(order), counts=counts,
                   pausedAtCompilerBoundary=paused,
                   statuses={kind: sum(state['records'].get(m, {}).get('status') == kind for m in order)
                             for kind in ['success', 'failed', 'blocked']})
    save(state_file, state)
    save(work/'last-run.json', summary)
    print(json.dumps(summary), flush=True)
    if paused:
        raise SystemExit(2)
    if counts['failed'] or counts['blocked']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
