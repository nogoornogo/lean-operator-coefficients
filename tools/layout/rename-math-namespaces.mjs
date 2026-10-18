import { readFileSync, writeFileSync, readdirSync, existsSync } from 'node:fs';
import { createHash } from 'node:crypto';

// A rename plan is frozen from the checked baseline's elaborated .ilean metadata.
// It is not a proof: focused/full rebuilds and unchanged axiom audits are required.
const walk = d => readdirSync(d, {withFileTypes:true}).flatMap(e =>
  e.isDirectory() ? walk(`${d}/${e.name}`) : [`${d}/${e.name}`]);
const files = ['Math','Physics','GUT'].flatMap(walk).filter(f => f.endsWith('.lean')).sort();
const mathNames = new Map(), otherNames = new Set(), openings = new Set(), mathUsers = new Set();
for (const file of files) {
  const metadata = `.lake/build/lib/lean/${file.replace(/\.lean$/, '.ilean')}`;
  if (!existsSync(metadata)) throw Error(`Missing baseline metadata: ${metadata}`);
  const data = JSON.parse(readFileSync(metadata, 'utf8'));
  for (const name of Object.keys(data.decls)) {
    if (file.startsWith('Math/')) mathNames.set(name, data.module);
    else otherNames.add(name);
  }
  for (const key of Object.keys(data.references)) {
    const ref = JSON.parse(key).c;
    if (ref?.m?.startsWith('Math.')) {
      mathNames.set(ref.n, ref.m);
      if (ref.n.startsWith('GUT.') || /_private\..*\.GUT\./.test(ref.n)) mathUsers.add(file);
    }
  }
  if (file.startsWith('Math/')) {
    for (const m of readFileSync(file,'utf8').matchAll(/^\s*namespace\s+(GUT(?:\.[\w]+)*)\s*$/gm)) openings.add(m[1]);
  }
}
const rename = n => {
  const next = n.replace(/^GUT(?=\.|$)/,'Math').replace(/(\._private\..*|^_private\..*)\.GUT(?=\.|$)/,'$1.Math');
  return next.includes('._aux_') ? next.replace(/_GUT_/g,'_Math_') : next;
};
const entries = [...mathNames].filter(([n]) => rename(n)!==n).map(([old,module]) => ({old,new:rename(old),module})).sort((a,b)=>a.old.localeCompare(b.old));
const direct = new Map(entries.map(e=>[e.old,e.new]));
const parents = new Set();
for (const {old} of entries) { let n=old; while (n.includes('.')) { n=n.slice(0,n.lastIndexOf('.')); if(n.startsWith('GUT.')) parents.add(n); } }
const shared = new Set([...parents].filter(n=>[...otherNames].some(x=>x===n||x.startsWith(n+'.'))));
const pure = [...parents].filter(n=>!shared.has(n)).sort((a,b)=>b.length-a.length);
const mixedRoots = new Set(['GUT.SU5', 'GUT.SUN']);
const ancestors = n => [...parents].filter(p=>!mixedRoots.has(p)&&(p===n||n.startsWith(p+'.'))).sort((a,b)=>b.length-a.length);
const qualified = n => {
  if(direct.has(n)) return direct.get(n);
  const prefix=pure.find(p=>n===p||n.startsWith(p+'.'));
  return prefix?n.replace(/^GUT(?=\.)/,'Math'):n;
};
const plans=[];
for(const file of files) {
  const old=readFileSync(file,'utf8');let text=old;
  if(file.startsWith('Math/')) {
    // Math has no Physics/GUT imports: every local GUT declaration is Math-owned.
    text=text.replace(/\bGUT(?=\.|\b)/g,'Math');
    for(const s of old.match(/"(?:[^"\\]|\\.)*"/g)||[])
      if(s.includes('GUT'))text=text.split(s.replace(/\bGUT/g,'Math')).join(s);
    for(const m of old.matchAll(/(?<!`)`(GUT(?:\.[\w]+)*)/g))
      if(!direct.has(m[1]))text=text.split('`'+m[1].replace(/^GUT/,'Math')).join('`'+m[1]);
    if(file==='Math/Audit/ImportOrigin.lean')text=old;
    else text=text.replace(/``GUT(?=\.|\b)/g,'``Math');
  } else {
    // Never change a model namespace opening or closing based on a pure prefix.
    text=text.split('\n').map(line=> {
      if(/^\s*(namespace|end)\s+GUT(?:\.|\s|$)/.test(line))return line;
      return line.replace(/\bGUT(?:\.[\p{L}\p{N}_']+)+/gu, qualified);
    }).join('\n');
    // Existing short names resolve through these additional namespace opens;
    // shared Physics/GUT declarations retain their original namespace.
    text=text.replace(/^(\s*namespace\s+(GUT(?:\.[\w]+)*)\s*)$/gm,(line,nothing,name)=>{
      const ns=ancestors(name);return ns.length?`${line}\nopen ${ns.map(n=>n.replace(/^GUT/,'Math')).join(' ')}`:line;
    });
    text=text.replace(/^(\s*open\s+)(.*)$/gm,(line,prefix,tail)=>{
      const extras=[...tail.matchAll(/\bGUT(?:\.[\w]+)+/g)].map(m=>m[0]).filter(n=>shared.has(n)&&!mixedRoots.has(n));
      return extras.length?`${prefix}${tail} ${extras.map(n=>n.replace(/^GUT/,'Math')).join(' ')}`:line;
    });
    // Opens are placed after imports and before the first declaration/namespace.
    const lines=text.split('\n');let last=-1;
    for(let i=0;i<lines.length;i++)if(/^import\s/.test(lines[i]))last=i;
    if(last>=0 && mathUsers.has(file))lines.splice(last+1,0,'','open Math');
    text=lines.join('\n');
  }
  if(text!==old)plans.push({file,old,text});
}
const manifest={kind:'elaborated-baseline-rename-plan',baseline:'fe2c195',
  input:'baseline .ilean declaration and reference metadata; validated by rebuild, not trusted as a proof',
  mathDeclarations:entries.length, sharedNamespaces:[...shared].sort(),entries,
  files:plans.map(p=>({file:p.file,oldHash:createHash('sha256').update(p.old).digest('hex')}))};
if(process.argv.includes('--apply')) {
  if(existsSync('docs/topics/math-namespaces/declaration-map.json'))
    throw Error('Rename plan already frozen; do not reapply against partially rebuilt metadata.');
  for(const p of plans)writeFileSync(p.file,p.text);
  writeFileSync('docs/topics/math-namespaces/declaration-map.json',JSON.stringify(manifest,null,2)+'\n');
}
console.log(JSON.stringify({declarations:entries.length,files:plans.length,shared:[...shared].sort(),applied:process.argv.includes('--apply')}));
