import { execFileSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, extname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const names = execFileSync('git', ['ls-files', '--cached', '--others', '--exclude-standard', '-z'],
  { cwd: root, encoding: 'utf8' }).split('\0');
const files = [...new Set(names)].filter(name => name.endsWith('.md') && existsSync(resolve(root, name)));

// Check the inline links and ATX headings used by this repository, excluding
// fenced examples. This is not a general Markdown parser or an external URL test.
function prose(text) {
  let fence;
  return text.split('\n').map(line => {
    const marker = line.match(/^\s{0,3}(`{3,}|~{3,})/);
    if (fence) {
      if (marker && marker[1][0] === fence[0] && marker[1].length >= fence.length) fence = undefined;
      return '';
    }
    if (marker) { fence = marker[1]; return ''; }
    return line;
  }).join('\n');
}

const headingCache = new Map();
function headings(file) {
  if (headingCache.has(file)) return headingCache.get(file);
  const text = prose(readFileSync(file, 'utf8'));
  const ids = new Set();
  for (const match of text.matchAll(/^#{1,6}\s+(.+?)\s*#*\s*$/gm)) {
    const plain = match[1].replace(/\[([^\]]+)\]\([^)]*\)/g, '$1').replace(/<[^>]*>/g, '');
    const base = plain.toLowerCase().replace(/[^\p{L}\p{N}\p{M}_ -]/gu, '').replace(/ /g, '-');
    let id = base;
    for (let i = 1; ids.has(id); i++) id = `${base}-${i}`;
    ids.add(id);
  }
  for (const match of text.matchAll(/\b(?:id|name)=["']([^"']+)["']/g)) ids.add(match[1]);
  headingCache.set(file, ids);
  return ids;
}

let checked = 0;
let fragments = 0;
const errors = [];
for (const name of files) {
  const file = resolve(root, name);
  const text = prose(readFileSync(file, 'utf8'));
  for (const match of text.matchAll(/\]\((?:<([^>]+)>|([^\s)]+))(?:\s+["'][^\n]*?["'])?\)/g)) {
    const url = match[1] || match[2];
    if (/^[a-z][a-z0-9+.-]*:|^\/\//i.test(url)) continue;
    const [rawPath, rawFragment] = url.split('#', 2);
    let target, fragment;
    try {
      target = rawPath ? resolve(dirname(file), decodeURIComponent(rawPath)) : file;
      fragment = rawFragment && decodeURIComponent(rawFragment);
    } catch {
      errors.push(`${name}: invalid URI encoding: ${url}`);
      continue;
    }
    checked++;
    if (!existsSync(target)) errors.push(`${name}: missing target: ${url}`);
    else if (fragment && extname(target) === '.md') {
      fragments++;
      if (!headings(target).has(fragment)) errors.push(`${name}: missing heading: ${url}`);
    }
  }
}
for (const error of errors) console.error(error);
console.log(`${files.length} Markdown files; ${checked} local inline links; ${fragments} heading fragments; ${errors.length} errors`);
process.exitCode = errors.length ? 1 : 0;
