import {readFileSync,writeFileSync,readdirSync} from 'node:fs';
const manifest=JSON.parse(readFileSync('docs/topics/math-namespaces/declaration-map.json','utf8'));
// Work records and scoped checkpoints retain the declaration names they checked.
const isCheckpoint=(f,text)=>f.startsWith('docs/topics/')||text.includes('Historical independent result:');
const direct=new Map(manifest.entries.map(e=>[e.old,e.new]));
const shared=new Set(manifest.sharedNamespaces);
const parents=new Set();for(const e of manifest.entries){let n=e.old;while(n.includes('.')){n=n.slice(0,n.lastIndexOf('.'));if(n.startsWith('GUT.'))parents.add(n);}}
const pure=[...parents].filter(n=>!shared.has(n)).sort((a,b)=>b.length-a.length);
const walk=d=>readdirSync(d,{withFileTypes:true}).flatMap(e=>e.isDirectory()?walk(d+'/'+e.name):[d+'/'+e.name]);
let changed=0;
for(const f of walk('docs').filter(f=>f.endsWith('.md'))){
 const old=readFileSync(f,'utf8');if(isCheckpoint(f,old))continue;const next=old.replace(/\bGUT(?:\.[\p{L}\p{N}_']+)+/gu,n=>{
  if(direct.has(n))return direct.get(n);
  return pure.some(p=>n===p||n.startsWith(p+'.'))?n.replace(/^GUT/,'Math'):n;
 });if(next!==old){writeFileSync(f,next);changed++;}
}console.log(JSON.stringify({updatedDocuments:changed,historicalDocuments:'unchanged; original declaration names retained as checkpoint evidence'}));
