import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { copyFileSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';

function fixture(run) {
  const root = mkdtempSync(join(tmpdir(), 'gut-doc-links-'));
  try {
    assert.equal(spawnSync('git', ['init', '--quiet', root]).status, 0);
    mkdirSync(join(root, 'tools/docs'), { recursive: true });
    const script = join(root, 'tools/docs/check-links.mjs');
    copyFileSync(new URL('./check-links.mjs', import.meta.url), script);
    const write = (name, text) => writeFileSync(join(root, name), text);
    const check = () => spawnSync(process.execPath, [script], { encoding: 'utf8' });
    run({ root, write, check });
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

test('checks new files, relative links, duplicate headings and escaped filenames', () => fixture(({ write, check }) => {
  write('target file.md', '# Repeated\n\n# Repeated\n');
  write('README.md', '[first](target%20file.md#repeated)\n[second](<target file.md#repeated-1>)\n');
  const result = check();
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /2 local inline links; 2 heading fragments; 0 errors/);
}));

test('rejects missing local files and heading fragments', () => fixture(({ write, check }) => {
  write('README.md', '# Present\n[bad file](missing.md)\n[bad heading](#absent)\n');
  const result = check();
  assert.equal(result.status, 1);
  assert.match(result.stderr, /missing target/);
  assert.match(result.stderr, /missing heading/);
}));

test('ignores fenced examples and external URLs', () => fixture(({ write, check }) => {
  write('README.md', '```md\n[example](missing.md)\n```\n~~~\n[another](absent.md)\n~~~\n[remote](https://example.invalid/)\n');
  const result = check();
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /0 local inline links/);
}));

test('skips tracked files deleted from the working tree', () => fixture(({ root, write, check }) => {
  write('removed.md', '[bad](missing.md)\n');
  assert.equal(spawnSync('git', ['-C', root, 'add', 'removed.md']).status, 0);
  rmSync(join(root, 'removed.md'));
  assert.equal(check().status, 0);
}));

test('reports malformed URI encoding instead of crashing', () => fixture(({ write, check }) => {
  write('README.md', '[bad](target%zz.md)\n');
  const result = check();
  assert.equal(result.status, 1);
  assert.match(result.stderr, /invalid URI encoding/);
}));
