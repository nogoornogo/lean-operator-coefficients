import assert from 'node:assert/strict';
import test from 'node:test';
import { imports, validate, originSource } from './check-layout.mjs';

const sources = () => ({
  Math: 'import Math.Algebra', 'Math.Algebra': 'import Mathlib.Algebra.Group.Basic',
  Physics: 'import Physics.Mass', 'Physics.Mass': 'import Math.Algebra',
  GUT: 'import Math\nimport Physics\nimport GUT.Model', 'GUT.Model': 'import Physics.Mass',
});

test('valid three-layer graph and external imports', () => assert.deepEqual(validate(sources()), []));
test('canonical implementations and legacy facades keep historical audit identities', () => {
  const generated = originSource({'GUT/OldMass.lean': 'Physics/Mass/Core.lean'},
    {'Physics/Mass.lean': 'Physics/Mass/Core.lean', 'Math/Input.lean': 'Math/Inputs/Core.lean'});
  assert.ok(generated.includes('| `Physics.Mass.Core => `GUT.OldMass'));
  assert.ok(generated.includes('| `Physics.Mass => `GUT.OldMass'));
  assert.ok(generated.includes('| `Math.Inputs.Core => `Math.Input'));
});
test('nested comments, strings, import all and whitespace', () => assert.deepEqual(imports(`
/- import GUT.Bad /- nested -/ -/
import all Math.Algebra -- comment
def s := "import GUT.Bad"
 public import Physics.Mass
`), ['Math.Algebra', 'Physics.Mass']));
test('split definitions retain the original audit identity', () => {
  const generated = originSource({'GUT/Old.lean': 'Physics/New.lean'},
    {'Physics/Old.lean': 'Physics/New.lean'},
    [{canonical: 'Physics/New.lean', definitions: 'Physics/New/Basic.lean'}]);
  assert.ok(generated.includes('| `Physics.New.Basic => `GUT.Old'));
});
test('reject both upward directions', () => {
  const s = sources(); s['Math.Algebra'] += '\nimport Physics.Mass';
  s['Physics.Mass'] += '\nimport GUT.Model';
  assert.equal(validate(s).filter(e => e.includes('upward')).length, 2);
});
test('multiple same-line imports are all checked', () => {
  const s = sources(); s['Math.Algebra'] = 'import Mathlib GUT.Model';
  assert.ok(validate(s).some(e => e.includes('upward import GUT.Model')));
});
test('missing local imports cannot use stale oleans', () => {
  const s = sources(); s['GUT.Model'] += '\nimport GUT.Missing';
  assert.ok(validate(s).some(e => e.includes('missing local import GUT.Missing')));
});
test('orphan source is not silently omitted from build', () => {
  const s = sources(); s['Math.Orphan'] = '';
  assert.ok(validate(s).includes('not covered by lake build: Math.Orphan'));
});
test('cycles are reported', () => {
  const s = sources(); s['Math.Algebra'] += '\nimport Math';
  assert.ok(validate(s).some(e => e.includes('cycle')));
});
test('all three Lake roots required', () => {
  const s = sources(); delete s.Physics;
  assert.ok(validate(s).includes('missing library root Physics'));
});
test('historical identity direction is new to old', () => {
  const generated = originSource({ 'GUT/Old.lean': 'Math/New.lean' });
  assert.ok(generated.includes('| `Math.New => `GUT.Old'));
  assert.ok(generated.includes('| name => name'));
});
