import { readFileSync, mkdirSync, writeFileSync, existsSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import * as d3 from 'd3';
import { JSDOM } from 'jsdom';

// Presentation of existing theorem conclusions; never an input to Lean proofs.
const root = fileURLToPath(new URL('../../', import.meta.url));
const { values } = parseArgs({ options: {
  check: { type: 'boolean', default: false },
  output: { type: 'string' },
} });
const output = values.output ? resolve(values.output) :
  resolve(root, 'docs/assets/readme/b1-minimum-dimensions.svg');
const minima = readFileSync(resolve(root,
  'Physics/StandardModel/Operators/Support/Dimension/SMB1ExactMinima.lean'), 'utf8');
const assignments = readFileSync(resolve(root,
  'Physics/StandardModel/Operators/Support/Decomposition/SMFiniteLeptonAssignments.lean'), 'utf8');

function statement(source, name) {
  const match = source.match(new RegExp(`theorem ${name}\\s*:\\s*([\\s\\S]*?)\\s*:=\\s*by`));
  if (!match) throw new Error(`Cannot read theorem statement: ${name}`);
  return match[1];
}
function finalCount(source, name) {
  const match = statement(source, name).match(/=\s*(\d+)\s*$/);
  if (!match) throw new Error(`Cannot read final count: ${name}`);
  return Number(match[1]);
}
const distribution = statement(minima, 'minimum_distribution');
const forbiddenMatch = distribution.match(/minimumCount\s+none\s*=\s*(\d+)/);
if (!forbiddenMatch) throw new Error('Missing None/forbidden count');
const forbidden = Number(forbiddenMatch[1]);
const bins = [...distribution.matchAll(/minimumCount\s*\(some\s+(\d+)\)\s*=\s*(\d+)/g)]
  .map(([, grade, count]) => ({ grade: Number(grade), count: Number(count) }));
if (!bins.length || new Set(bins.map(b => b.grade)).size !== bins.length ||
    bins.some(b => b.grade % 2 !== 0 || b.grade <= 0 || b.count <= 0)) {
  throw new Error('Expected distinct positive even doubled grades and positive counts');
}
bins.sort((a, b) => a.grade - b.grade);
const allowed = finalCount(minima, 'classified_count');
const total = finalCount(assignments, 'rows_length');
if (d3.sum(bins, b => b.count) !== allowed || allowed + forbidden !== total) {
  throw new Error('Theorem counts do not form the stated partition');
}

// JS reimplementation of the displayed Lean domain and B1 neutrality criterion.
// Fixed bounds need review if candidatePairs or leptonRange changes.
let domainCount = 0;
let neutralCount = 0;
for (let k = 2; k <= 12; k++) {
  for (let q = 0; q < k; q++) {
    for (let l = 0; l < k; l++) {
      if ((3 * q + l) % k === 0) continue;
      domainCount++;
      if (d3.range(-17, 18, 2).some(L => (3 * q + L * l) % k === 0)) neutralCount++;
    }
  }
}
if (domainCount !== total || neutralCount !== allowed) {
  throw new Error('README domain/charge criterion disagrees with theorem counts');
}

const document = new JSDOM('<!doctype html><html><body></body></html>').window.document;
const svg = d3.select(document.body).append('svg')
  .attr('xmlns', 'http://www.w3.org/2000/svg')
  .attr('width', 1000).attr('height', 460).attr('viewBox', '0 0 1000 460')
  .attr('role', 'img').attr('aria-labelledby', 'title description');
svg.append('title').attr('id', 'title').text('Fixed SM/Higgs structural classification');
svg.append('desc').attr('id', 'description').text(
  `Derivative-free absolute baryon-number change one, fixed three-generation ` +
  `neutral-Higgs scalar cyclic q/l input. ${total} labeled inputs: ` +
  `${allowed} allowed, ${forbidden} forbidden at all degrees. Exact minimum ` +
  `engineering dimensions and counts: ${bins.map(b => `${b.grade / 2}: ${b.count}`).join('; ')}. ` +
  'Forbidden inputs have no finite minimum. Data: ' +
  'Physics.SMB1ExactMinima.minimum_distribution and classified_count; ' +
  'Physics.SMFiniteLeptonAssignments.rows_length. Dimensions are half the Lean grades.');
svg.append('style').text(
  'text{font-family:Arial,Helvetica,sans-serif;fill:#1d2d40}' +
  '.domain,.tick line{stroke:#9aa8b8}.tick text{fill:#45566b}' +
  '.grid line{stroke:#e6ebf1}.grid .domain{display:none}');
svg.append('rect').attr('width', 1000).attr('height', 460)
  .attr('rx', 10).attr('fill', '#fff').attr('stroke', '#d9e0e8');
const text = (x, y, label, size = 14) => svg.append('text')
  .attr('x', x).attr('y', y).attr('font-size', size).text(label);
text(30, 38, 'Fixed SM/Higgs structural classification', 25).attr('font-weight', 600);
text(30, 65, 'Derivative-free |ΔB| = 1 · three generations · neutral Higgs · scalar cyclic q/l actions', 15);
text(30, 111, `${total} labeled inputs`, 18).attr('font-weight', 600);
text(405, 111, `Exact minima of the ${allowed} allowed inputs`, 18).attr('font-weight', 600);

const xSummary = d3.scaleLinear().domain([0, total]).range([0, 290]);
for (const [i, row] of [
  { label: 'Allowed', count: allowed, color: '#2466a3' },
  { label: 'Forbidden at all degrees', count: forbidden, color: '#73808e' },
].entries()) {
  const y = 153 + i * 85;
  text(30, y, row.label, 15);
  svg.append('rect').attr('x', 30).attr('y', y + 12)
    .attr('width', xSummary(row.count)).attr('height', 28).attr('fill', row.color);
  text(40 + xSummary(row.count), y + 32, row.count, 16).attr('font-weight', 600);
}
text(30, 340, 'Forbidden inputs have', 14);
text(30, 361, 'no finite minimum dimension.', 14);

const x = d3.scaleBand().domain(bins.map(b => String(b.grade / 2)))
  .range([415, 970]).padding(0.28);
const ceiling = Math.ceil(d3.max(bins, b => b.count) / 20) * 20;
const y = d3.scaleLinear().domain([0, ceiling]).range([340, 148]);
svg.append('g').attr('class', 'grid').attr('transform', 'translate(405,0)')
  .call(d3.axisLeft(y).ticks(5).tickSize(-565).tickFormat(() => ''));
svg.append('g').attr('transform', 'translate(405,0)')
  .call(d3.axisLeft(y).ticks(5).tickSize(4)).attr('font-size', 12);
svg.append('g').attr('transform', 'translate(0,340)')
  .call(d3.axisBottom(x).tickSize(0).tickPadding(10)).attr('font-size', 14);
svg.append('g').selectAll('rect').data(bins).join('rect')
  .attr('x', b => x(String(b.grade / 2))).attr('y', b => y(b.count))
  .attr('width', x.bandwidth()).attr('height', b => y(0) - y(b.count)).attr('fill', '#2466a3');
svg.append('g').selectAll('text').data(bins).join('text')
  .attr('x', b => x(String(b.grade / 2)) + x.bandwidth() / 2)
  .attr('y', b => y(b.count) - 7).attr('text-anchor', 'middle')
  .attr('font-size', 13).text(b => b.count);
text(383, 140, 'Inputs', 12).attr('text-anchor', 'end');
text(692, 389, 'Minimum engineering dimension', 15).attr('text-anchor', 'middle');
text(30, 423, 'Domain: 2 ≤ k ≤ 12, 0 ≤ q,l < k, and (3q+l) mod k ≠ 0.', 13);
text(30, 446, 'Source: SMB1ExactMinima.minimum_distribution; engineering dimension = Lean grade / 2.', 12);

const result = svg.node().outerHTML + '\n';
if (values.check) {
  if (!existsSync(output) || readFileSync(output, 'utf8') !== result) {
    throw new Error('Figure is missing or stale; rerun the generator without --check');
  }
  console.log(`PASS: figure matches theorem data; ${total} inputs, ${allowed} allowed, ${forbidden} forbidden`);
} else {
  mkdirSync(dirname(output), { recursive: true });
  writeFileSync(output, result);
  console.log('Wrote source-derived structural classification figure.');
}
