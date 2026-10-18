import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

// Explicit namespace-opening inventory, not an elaborated declaration registry.
// Qualified declarations and implicit namespace resolution require Lean checks.
const walk = dir => readdirSync(dir, { withFileTypes: true }).flatMap(entry =>
  entry.isDirectory() ? walk(join(dir, entry.name)) : [join(dir, entry.name)]);
const files = ['Math', 'Physics', 'GUT'].flatMap(walk).filter(f => f.endsWith('.lean')).sort();
const openings = [];
for (const file of files) {
  const lines = readFileSync(file, 'utf8').split('\n');
  let commentDepth = 0;
  lines.forEach((line, i) => {
    let prose = '';
    for (let j = 0; j < line.length; j++) {
      const pair = line.slice(j, j + 2);
      if (pair === '/-') { commentDepth++; j++; continue; }
      if (pair === '-/' && commentDepth) { commentDepth--; j++; continue; }
      if (!commentDepth && pair === '--') break;
      if (!commentDepth) prose += line[j];
    }
    const match = prose.match(/^\s*namespace\s+([\w.]+)/);
    if (match) openings.push({ file, line: i + 1, layer: file.split('/')[0], name: match[1] });
  });
}
const names = [...new Set(openings.filter(x => x.layer === 'Math' && /^GUT(?:\.|$)/.test(x.name)).map(x => x.name))].sort();
const entries = names.map(old => ({
  old, proposed: old.replace(/^GUT/, 'Math'),
  definitions: openings.filter(x => x.layer === 'Math' && x.name === old),
  otherLayerOpenings: openings.filter(x => x.layer !== 'Math' &&
    (x.name === old || x.name.startsWith(old + '.') ||
      (x.name !== 'GUT' && old.startsWith(x.name + '.')))),
  targetOpenings: openings.filter(x => x.name === old.replace(/^GUT/, 'Math')),
}));
console.log(JSON.stringify({
  kind: 'explicit-opening-inventory',
  limitation: 'Not an elaborated declaration map; shared namespaces require ownership resolution before rewriting.',
  sourceFiles: files.length, mathFiles: files.filter(f => f.startsWith('Math/')).length,
  mathLegacyFiles: new Set(openings.filter(x => x.layer === 'Math' && /^GUT(?:\.|$)/.test(x.name)).map(x => x.file)).size,
  entries, openings,
}, null, 2));
