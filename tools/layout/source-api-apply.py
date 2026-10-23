#!/usr/bin/env python3
"""Apply the reviewed source-api-v1 plan, preserving old import/name facades.

Run once on its recorded input. A separate post-build checker verifies the
result. This script never changes proof assumptions, limits or allowlists.
"""
import hashlib
import json
import re
import subprocess
import importlib.util
from pathlib import Path
from source_api_registry import load_plan, bridge_source

TOPIC = Path('docs/topics/source-api-compatibility')
VERSION = 'source-api-v1'


def module(file):
    return str(Path(file).with_suffix('')).replace('/', '.')


def facade_source(path, entries, modules):
    new_mod = module(path['new'])
    deps = [d for d in path['dependencies'] if d in modules] if entries or path['old'].startswith('Physics/') else []
    text = f'import {new_mod}\n'
    text += ''.join(f'import {d}\n' for d in dict.fromkeys(deps))
    if entries:
        text += 'import Math.Lean.Compatibility\n'
    text += f'\ndeprecated_module "Use {new_mod} instead." (since := "{VERSION}")\n'
    if entries:
        text += '\ncompatibility_declarations [\n'
        text += ',\n'.join(f'  {e["old"]} => {e["new"]}' for e in entries)
        text += '\n]\n\n'
        text += ''.join(f'assert_compatible {e["old"]} => {e["new"]}\n' for e in entries)
    return text


def code_map(source, transform):
    """Transform code while retaining nested comments and string literals."""
    chunks, start, i = [], 0, 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair in ('--', '/-') or source[i] == '"':
            chunks.append(transform(source[start:i]))
            begin = i
            if pair == '--':
                end = source.find('\n', i)
                i = len(source) if end < 0 else end
            elif pair == '/-':
                depth, i = 1, i + 2
                while i < len(source) and depth:
                    if source[i:i + 2] == '/-':
                        depth += 1
                        i += 2
                    elif source[i:i + 2] == '-/':
                        depth -= 1
                        i += 2
                    else:
                        i += 1
            else:
                i += 1
                while i < len(source):
                    if source[i] == '\\':
                        i += 2
                    elif source[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
            chunks.append(source[begin:i])
            start = i
        else:
            i += 1
    chunks.append(transform(source[start:]))
    return ''.join(chunks)


def protect_module_audits(source):
    """Import exclusions concern historical MODULE names, not namespaces."""
    lines = source.splitlines(keepends=True)
    saved, i = [], 0
    while i < len(lines):
        if re.search(r'for mod in .*moduleNames', lines[i]):
            indent = len(lines[i]) - len(lines[i].lstrip())
            j = i + 1
            while j < len(lines) and (not lines[j].strip() or
                    len(lines[j]) - len(lines[j].lstrip()) > indent):
                j += 1
            key = f'__SOURCE_API_MODULE_AUDIT_{len(saved)}__\n'
            saved.append((key, ''.join(lines[i:j])))
            lines[i:j] = [key]
        i += 1
    return ''.join(lines), saved


def apply():
    plan = load_plan()
    paths = plan['paths']
    contents = {}
    for p in paths:
        raw = Path(p['input']).read_bytes()
        if hashlib.sha256(raw).hexdigest() != p['sha256']:
            raise SystemExit(f'Input changed after freeze: {p["input"]}')
        contents[p['old']] = raw.decode()
    moves = {p['old']: p['new'] for p in paths if p['old'] != p['new']}
    modules = {module(a): module(b) for a, b in moves.items()}
    direct = {e['old']: e['new'] for e in plan['entries']}
    bridges = {module(b['old']): b for b in plan.get('importBridges', [])}
    su5_users = set(plan.get('namespaceUsers', {}).get('GUT.SU5', []))
    physics = set(n for n in plan['physicsOwned'] if n.startswith('GUT.'))
    parents, shared = set(), set()
    for names, dest in [(physics, parents), (plan['applicationOwned'], shared)]:
        for name in names:
            while '.' in name:
                name = name.rsplit('.', 1)[0]
                if name.startswith('GUT.'):
                    dest.add(name)
    pure = parents - shared

    def qualified(match):
        name = match.group()
        if name in direct:
            return direct[name]
        prefix = name
        while '.' in prefix:
            if prefix in pure:
                return 'Physics.' + name[4:]
            prefix = prefix.rsplit('.', 1)[0]
        return name

    token = re.compile(r'\bGUT(?:\.[\w\u2080-\u209f\u03b1-\u03c9\u1d00-\u1dff\']+)*')

    def imports(source):
        def replacement(match):
            if match[2] in bridges:
                return '\n'.join('import ' + dep for dep in bridges[match[2]]['canonicalImports'])
            return match[1] + modules.get(match[2], match[2])
        return re.sub(r'^(import\s+)([\w.]+)',
                      replacement, source, flags=re.M)

    def module_literals(source):
        source, protected = protect_module_audits(source)
        source = code_map(source, lambda code: re.sub(r'(?<!`)`([\w.]+)',
            lambda m: '`' + modules.get(m[1], m[1]), code))
        for key, text in protected:
            source = source.replace(key, text)
        return source

    for old, source in contents.items():
        if old == 'Math/Audit/ImportOrigin.lean':
            continue
        source = module_literals(imports(source))
        if moves.get(old, old).startswith('Physics/'):
            source, protected = protect_module_audits(source)
            source = code_map(source, lambda code: token.sub(
                lambda m: 'Physics' + m[0][3:], code))
            for key, text in protected:
                source = source.replace(key, text)
            source = source.replace('logInfo m!"GUT.', 'logInfo m!"Physics.')
            source = source.replace('These primitives retain their original declaration names. They need no',
                                    'These primitives need no')
        elif old.startswith('GUT/'):
            # GUT-owned declarations stay put, including extensions of the six
            # namespace families shared with Physics. Opens recover short names.
            lines = source.splitlines(keepends=True)
            for i, line in enumerate(lines):
                ns = re.match(r'\s*(namespace|end)\s+(GUT[\w.]*)\s*$', line)
                if ns:
                    if ns[1] == 'namespace':
                        ancestry = sorted((p for p in parents if ns[2] == p or
                                           ns[2].startswith(p + '.')), key=len, reverse=True)
                        ancestry = [p for p in ancestry if p not in ('GUT.SU5', 'GUT.SUN')]
                        if ancestry:
                            lines[i] += 'open ' + ' '.join('Physics.' + p[4:] for p in ancestry) + '\n'
                        if ns[2].startswith('GUT.SU5.') and old in su5_users:
                            lines[i] += 'open Physics.SU5\n'
                    continue
                lines[i] = code_map(line, lambda code: token.sub(qualified, code))
                opened = re.match(r'\s*open\s+(.+)', line)
                if opened:
                    extras = [n for n in token.findall(opened[1]) if n in shared & parents
                              and (n != 'GUT.SU5' or old in su5_users)]
                    if extras:
                        if re.search(r'[()]|\bhiding\b|\brenaming\b', opened[1]):
                            raise SystemExit(f'Shared restricted open requires an explicit repair: {old}')
                        for name in extras:
                            pattern = re.compile(r'(?<![\w.])' + re.escape(name) + r'(?![\w.])')
                            lines[i] = code_map(lines[i], lambda code: pattern.sub(
                                name + ' Physics.' + name[4:], code))
            source = ''.join(lines)
            if old in plan['physicsUsers']:
                last_import = max((m.end() for m in re.finditer(r'^import[^\n]*\n', source, re.M)), default=0)
                source = source[:last_import] + '\nopen Physics\n' + source[last_import:]
        dest = Path(moves.get(old, old))
        dest.parent.mkdir(parents=True, exist_ok=True)
        if old in moves:
            source = source.rstrip() + '\n'
        dest.write_text(source)

    if (TOPIC / 'proof-repairs.json').exists():
        spec = importlib.util.spec_from_file_location('source_api_repairs', 'tools/layout/source-api-repairs.py')
        repairs = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(repairs)
        repairs.apply_repairs()

    for bridge in bridges.values():
        Path(bridge['old']).write_text(bridge_source(bridge, plan['migration']))

    by_module = {}
    for e in plan['entries']:
        by_module.setdefault(e['module'], []).append(e)
    for p in paths:
        if p['old'] == p['new']:
            continue
        Path(p['old']).write_text(facade_source(p, by_module.get(module(p['old']), []), modules))

    for root in ('Math', 'Physics', 'GUT'):
        file = Path(root + '.lean')
        # Retain legacy facades in aggregate coverage; internal code uses new routes.
        text = imports(file.read_text())
        present = set(re.findall(r'^import ([\w.]+)', text, re.M))
        extras = sorted(module(str(p)) for p in Path(root).rglob('*.lean') if module(str(p)) not in present)
        text += ''.join(f'import {m}\n' for m in extras)
        seen = set()
        lines = []
        for line in text.splitlines(keepends=True):
            if line.startswith('import '):
                if line in seen:
                    continue
                seen.add(line)
            lines.append(line)
        file.write_text(''.join(lines))

    origin_file = Path('tools/layout/source-map.json')
    origin = json.loads(origin_file.read_text())
    for key, value in origin.items():
        origin[key] = moves.get(value, value)
    origin_file.write_text(json.dumps(origin, indent=2) + '\n')
    subprocess.run(['node', '--input-type=module', '-e', '''
import {readFileSync,writeFileSync} from 'node:fs';
import {originSource,compatibilityPaths,declarationSplits} from './tools/layout/check-layout.mjs';
writeFileSync('Math/Audit/ImportOrigin.lean',originSource(
  JSON.parse(readFileSync('tools/layout/source-map.json','utf8')),compatibilityPaths('.'),declarationSplits('.')));
'''], check=True)
    print(f'Applied {len(moves)} canonical moves; legacy facades and {len(direct)} aliases retained')


if __name__ == '__main__':
    apply()
