import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const roots = ['Math', 'Physics', 'GUT'];
const rootOf = name => name.split('.')[0];
export const moduleName = file => file.slice(0, -5).replaceAll('/', '.');

// Remove nested Lean comments and strings before reading import commands.
export function imports(source) {
  let clean = '', depth = 0, string = false;
  for (let i = 0; i < source.length; i++) {
    const pair = source.slice(i, i + 2), c = source[i];
    if (depth) {
      if (pair === '/-') { depth++; i++; }
      else if (pair === '-/') { depth--; i++; }
      else if (c === '\n') clean += '\n';
    } else if (string) {
      if (c === '\\') i++;
      else if (c === '"') string = false;
      else if (c === '\n') clean += '\n';
    } else if (pair === '/-') { depth = 1; clean += ' '; i++; }
    else if (pair === '--') {
      while (i < source.length && source[i] !== '\n') i++;
      clean += '\n';
    } else if (c === '"') { string = true; clean += ' '; }
    else clean += c;
  }
  return [...clean.matchAll(/^\s*(?:public\s+|private\s+)?(?:meta\s+)?import[ \t]+(?:all[ \t]+)?([A-Za-z_][\w.]*(?:[ \t]+[A-Za-z_][\w.]*)*)/gm)]
    .flatMap(match => match[1].split(/[ \t]+/));
}

export function validate(sources) {
  const graph = new Map(Object.entries(sources).map(([name, text]) => [name, imports(text)]));
  const errors = [], rank = { Math: 0, Physics: 1, GUT: 2 };
  for (const [name, deps] of graph) for (const dep of deps) {
    if (!(rootOf(dep) in rank)) continue;
    if (!graph.has(dep)) errors.push(`${name}: missing local import ${dep}`);
    if (rank[rootOf(name)] < rank[rootOf(dep)]) errors.push(`${name}: upward import ${dep}`);
  }
  const visited = new Set(), active = new Set();
  function visit(name) {
    if (active.has(name)) { errors.push(`import cycle at ${name}`); return; }
    if (visited.has(name) || !graph.has(name)) return;
    visited.add(name); active.add(name);
    for (const dep of graph.get(name)) visit(dep);
    active.delete(name);
  }
  visit('GUT');
  for (const name of graph.keys()) if (!visited.has(name)) errors.push(`not covered by lake build: ${name}`);
  // Check orphan cycles as well, without treating them as aggregate coverage.
  for (const name of graph.keys()) visit(name);
  for (const root of roots) if (!graph.has(root)) errors.push(`missing library root ${root}`);
  return errors;
}

export function collectSources(root) {
  const sources = {};
  function walk(dir) {
    for (const entry of fs.readdirSync(path.join(root, dir), { withFileTypes: true })) {
      const file = path.posix.join(dir, entry.name);
      if (entry.isDirectory()) walk(file);
      else if (file.endsWith('.lean')) sources[moduleName(file)] = fs.readFileSync(path.join(root, file), 'utf8');
    }
  }
  for (const r of roots) {
    sources[r] = fs.readFileSync(path.join(root, r + '.lean'), 'utf8'); walk(r);
  }
  return sources;
}

export function compatibilityPaths(root) {
  const file = path.join(root, 'docs/topics/source-api-compatibility/layout-plan.json');
  if (!fs.existsSync(file)) return {};
  const paths = new Map(JSON.parse(fs.readFileSync(file, 'utf8')).paths.map(p => [p.old, p.new]));
  const extra = path.join(root, 'docs/topics/source-api-compatibility/registry-addendum.json');
  if (fs.existsSync(extra))
    for (const p of JSON.parse(fs.readFileSync(extra, 'utf8')).paths) paths.set(p.old, p.new);
  return Object.fromEntries([...paths].filter(([old, current]) => old !== current));
}

export function declarationSplits(root) {
  const file = path.join(root, 'docs/topics/source-api-compatibility/proof-repairs.json');
  return fs.existsSync(file) ? JSON.parse(fs.readFileSync(file, 'utf8')) : [];
}

export function originSource(mapping, compatibility = {}, splits = []) {
  const origins = new Map(Object.entries(mapping).map(([a, b]) => [moduleName(b), moduleName(a)]));
  for (const [old, current] of Object.entries(compatibility)) {
    const legacy = moduleName(old), canonical = moduleName(current);
    const original = origins.get(canonical) ?? legacy;
    origins.set(canonical, original);
    if (legacy !== original) origins.set(legacy, original);
  }
  for (const split of splits) {
    const source = moduleName(split.canonical), target = moduleName(split.definitions);
    origins.set(target, origins.get(source) ?? source);
  }
  return 'import Lean\n\n/-! Historical import-boundary audits use original module identities so a\nfile relocation cannot silently bypass an existing exclusion. Declaration\nnames and axiom allowlists are not changed. Generated from the original and compatible path maps. -/\n\nnamespace SourceLayout\n\ndef originalModule : Lean.Name → Lean.Name\n' +
    [...origins].map(([current, original]) => `  | \`${current} => \`${original}`).join('\n') +
    '\n  | name => name\n\nend SourceLayout\n';
}

function main() {
  const root = fileURLToPath(new URL('../../', import.meta.url));
  const sources = collectSources(root), errors = validate(sources);
  const map = JSON.parse(fs.readFileSync(path.join(root, 'tools/layout/source-map.json'), 'utf8'));
  for (const [old, target] of Object.entries(map)) {
    if (fs.existsSync(path.join(root, old))) errors.push(`obsolete source still present: ${old}`);
    if (!(moduleName(target) in sources)) errors.push(`relocation target missing: ${target}`);
  }
  if (sources['Math.Audit.ImportOrigin'] !== originSource(map, compatibilityPaths(root), declarationSplits(root)))
    errors.push('ImportOrigin is out of sync with the original and compatible path maps');
  for (const [name, text] of Object.entries(sources)) {
    if (text.includes('header.moduleNames') && !text.includes('SourceLayout.originalModule mod')) {
      errors.push(`${name}: historical import audit does not normalize relocated modules`);
    }
  }
  if (errors.length) { console.error(errors.join('\n')); process.exitCode = 1; }
  else console.log(`${Object.keys(sources).length} modules; layers, local imports, cycles, aggregate coverage and relocation audits OK`);
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
