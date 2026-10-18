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
  for (const name of Object.keys(data.decls))
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
const missing = map.entries.filter(e => !metadata.get(e.module)?.has(e.new) && !references.has(e.new));
if (missing.length) throw Error(`Missing migrated names (${missing.length}): ${JSON.stringify(missing.slice(0, 10))}`);
console.log(`${metadata.size} Math modules; ${map.entries.length} migrated names verified in rebuilt metadata; no legacy Math-owned declarations`);
