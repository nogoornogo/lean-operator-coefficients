import { readFileSync, readdirSync } from 'node:fs';

// Post-build metadata consistency check, not a replacement for Lean/audit builds.
const walk = d => readdirSync(d, { withFileTypes: true }).flatMap(e =>
  e.isDirectory() ? walk(`${d}/${e.name}`) : [`${d}/${e.name}`]);
const metadata = new Map();
const references = new Set();
for (const file of walk('Math').filter(f => f.endsWith('.lean'))) {
  const data = JSON.parse(readFileSync(`.lake/build/lib/lean/${file.replace(/\.lean$/, '.ilean')}`, 'utf8'));
  const names = new Set(Object.keys(data.decls));
  for (const key of Object.keys(data.references)) {
    const c = JSON.parse(key).c;
    if (c?.m?.startsWith('Math.')) references.add(c.n);
    if (c?.m === data.module) names.add(c.n);
  }
  for (const name of names)
    if (name.startsWith('GUT.') || /_private\..*\.GUT\./.test(name))
      throw Error(`Legacy Math-owned declaration: ${data.module}: ${name}`);
  metadata.set(data.module, names);
}
for (const file of ['Physics', 'GUT'].flatMap(walk).filter(f => f.endsWith('.lean'))) {
  const data = JSON.parse(readFileSync(`.lake/build/lib/lean/${file.replace(/\.lean$/, '.ilean')}`, 'utf8'));
  for (const key of Object.keys(data.references)) {
    const c = JSON.parse(key).c;
    if (c?.m?.startsWith('Math.')) references.add(c.n);
  }
}
const map = JSON.parse(readFileSync('docs/topics/math-namespaces/declaration-map.json', 'utf8'));
const layout = JSON.parse(readFileSync('docs/topics/source-api-compatibility/layout-plan.json', 'utf8'));
const moved = new Map(layout.paths.map(p => [p.old.slice(0, -5).replaceAll('/', '.'),
  p.new.slice(0, -5).replaceAll('/', '.')]));
// Preserve every frozen correspondence, including the compiler's private-name
// module prefix. A facade has no original implementation declarations.
const repairs = JSON.parse(readFileSync('docs/topics/source-api-compatibility/namespace-check-repairs.json', 'utf8'));
const used = new Set();
const missing = map.entries.filter(e => {
  const module = moved.get(e.module) ?? e.module;
  let name = e.new.replace(`_private.${e.module}.`, `_private.${module}.`);
  // Lean also encodes the module path inside private macro implementation names.
  if (name.startsWith('_private.') && name.includes('._aux_'))
    name = name.replaceAll(e.module.replaceAll('.', '_'), module.replaceAll('.', '_'));
  const repair = repairs.find(r => r.module === e.module && r.historical === e.new);
  if (repair) {
    used.add(repair);
    name = repair.baseline;
  }
  return !metadata.get(module)?.has(name) && !references.has(name);
});
if (used.size !== repairs.length) throw Error('Unused historical namespace inventory correction');
if (missing.length) throw Error(`Missing migrated names (${missing.length}): ${JSON.stringify(missing.slice(0, 10))}`);
console.log(`${metadata.size} Math modules; ${map.entries.length} historical correspondences verified (including ${repairs.length} recorded pre-baseline renamings) in rebuilt metadata; no legacy Math-owned declarations`);
