#!/usr/bin/env python3
"""Emit individually kernel-checked coefficient candidates and their composition.

Uses the independent exact Python diagnostic only to suggest integer values.
Every suggested coefficient is a closed decide +kernel goal; no CSV or Python
result is imported as a theorem premise. Build SMGroupedCharacter first.
"""
import argparse
import ast
from functools import lru_cache
import re
import csv
from pathlib import Path
import runpy

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('species', type=int)
parser.add_argument('fermions', type=int)
parser.add_argument('m', type=int)
parser.add_argument('delta', type=int)
parser.add_argument('--index', type=int, help='emit only one coefficient probe (0..47)')
parser.add_argument('--chunk', type=int, help='emit four coefficients (chunk 0..11)')
parser.add_argument('--chain-prefix', metavar='IMPORT_PREFIX',
                    help='make chunk N import IMPORT_PREFIXPart(N-1)')
parser.add_argument('--compose-only', metavar='IMPORT_PREFIX',
                    help='compose twelve existing IMPORT_PREFIXPartN modules')
parser.add_argument('--split-depth', type=int, default=0,
                    help='share checked recurrence states through this many groups (0..12)')
args = parser.parse_args()
key = args.species, args.fermions, args.m, args.delta
with Path(__file__).with_name('neutral-sparse-results.csv').open(newline='') as stream:
    candidates = [row for row in csv.DictReader(stream)
                  if tuple(int(row[k]) for k in ('species', 'fermions', 'm', 'delta')) == key]
if len(candidates) != 1:
    parser.error('expected one key in the bounded 107-row candidate output')
if args.index is not None and not 0 <= args.index < 48:
    parser.error('--index must lie in 0..47')
if not 0 <= args.split_depth <= 12:
    parser.error('--split-depth must lie in 0..12')
if args.chunk is not None and not 0 <= args.chunk < 12:
    parser.error('--chunk must lie in 0..11')
if sum((args.index is not None, args.chunk is not None, args.compose_only is not None)) > 1:
    parser.error('--index, --chunk and --compose-only are mutually exclusive')
if args.chain_prefix and args.chunk is None:
    parser.error('--chain-prefix requires --chunk')
row = candidates[0]
diagnostic = runpy.run_path(str(Path(__file__).with_name('check-sm-weyl.py')))
coefficient = diagnostic['coefficient']
colors = ((0, 0), (1, -1), (1, 2), (3, 0), (3, 3), (4, 2))
points = [(a, b, weak, left, right, 3*args.delta)
          for a, b in colors for left in (0, 2) for right in (0, 2)
          for weak in (-args.m, args.m+2)]
prefix = f's{args.species}_n{args.fermions}_m{args.m}_d' + (
    f'neg{-args.delta}' if args.delta < 0 else str(args.delta))
if args.compose_only:
    for chunk in range(12):
        print(f'import {args.compose_only}Part{chunk}')
elif args.chain_prefix and args.chunk:
    print(f'import {args.chain_prefix}Part{args.chunk-1}')
else:
    print('import Physics.StandardModel.Operators.SMGroupedCharacter')
if args.index is None and args.chunk is None:
    print('import Physics.StandardModel.Operators.SMCoefficientAssembly')
print('namespace GUT.SMNeutralCoefficientCertificate')
print('open SMNeutralSparseRanks SMGroupedCharacter')
print('/- Generated numbers are candidates, each checked independently below. -/')
def point_text(w):
    return '(' + ','.join(f'({x})' for x in w) + ')'


selected = [(i, w) for i, w in enumerate(points)
            if (args.index is None or i == args.index)
            and (args.chunk is None or i//4 == args.chunk)
            and not args.compose_only]
if args.split_depth:
    source = Path(__file__).resolve().parents[2] / 'Physics/StandardModel/Operators/SMGroupedCharacter.lean'
    matches = dict(re.findall(r'  \| (\d+) => (\[.*\])', source.read_text()))
    weights = ast.literal_eval(matches[str(args.species)])
    sign = 1 if args.species < 5 else -1

    def probes(n, w):
        a, b, weak, left, right, hyper = w
        active, inactive = (left, right) if args.species in (0, 3) else (right, left)
        return (n-2*sign*a+sign*b, n+sign*a-2*sign*b, n+sign*a+sign*b,
                n+weak, n-weak, n+active, n-active, inactive,
                diagnostic['HYPER'][args.species]*n+hyper)

    limits = []
    for level in range(len(weights)+1):
        values = [probes(1, w) for w in weights[level:]]
        limits.append([(3*sum(min(0, v[j]) for v in values),
                        3*sum(max(0, v[j]) for v in values)) for j in range(9)])

    def possible(level, n, w):
        return all(lo <= x <= hi for x, (lo, hi) in zip(probes(n, w), limits[level]))

    def children(level, n, w):
        return [(level+1, n-k, tuple(x-k*y for x, y in zip(w, weights[level])))
                for k in range(min(n, 3)+1)]

    @lru_cache(None)
    def value(level, n, w):
        if not possible(level, n, w):
            return 0
        if level == len(weights):
            return int(n == 0 and all(x == 0 for x in w))
        return sum((1, 3, 3, 1)[k]*value(*child)
                   for k, child in enumerate(children(level, n, w)))

    states = set()

    def visit(state):
        if state in states:
            return
        states.add(state)
        level, n, w = state
        if level < min(args.split_depth, len(weights)) and possible(*state):
            for child in children(*state):
                visit(child)

    for _, w in selected:
        visit((0, args.fermions, w))
    ordered = sorted(states, key=lambda state: (-state[0], state[1], state[2]))
    names = {state: f'{prefix}_state{i}' for i, state in enumerate(ordered)}
    for state in ordered:
        level, n, w = state
        head = (f'Math.BoundedExteriorCoefficient.compute (tests {args.species}) '
                f'((groups {args.species}).drop {level}) {n} {point_text(w)}')
        print(f'theorem {names[state]} : {head} = {value(*state)} := by')
        if level >= min(args.split_depth, len(weights)) or not possible(*state):
            print('  decide +kernel')
        else:
            tail = f'({point_text(weights[level])} :: (groups {args.species}).drop {level+1})'
            print(f'  change Math.BoundedExteriorCoefficient.compute (tests {args.species}) '
                  f'{tail} {n} {point_text(w)} = {value(*state)}')
            print('  rw [Math.BoundedExteriorCoefficient.compute_cons]')
            print(f'  have hb : Math.BoundedExteriorCoefficient.possible '
                  f'(Math.BoundedExteriorCoefficient.bounds (tests {args.species}) '
                  f'{tail}) {n} {point_text(w)} = true := by')
            print('    decide +kernel')
            print('  rw [hb]')
            expressions = []
            for k, (lev, degree, target) in enumerate(children(*state)):
                expr = (f'Math.BoundedExteriorCoefficient.compute (tests {args.species}) '
                        f'((groups {args.species}).drop {lev}) {degree} {point_text(target)}')
                expressions.append(expr if k in (0, 3) else '3 * (' + expr + ')')
            print('  change ' + ' + '.join(expressions) + f' = {value(*state)}')
            print('  rw [' + ','.join(names[c] for c in children(*state)) + ']')
            print('  decide +kernel')
    for i, w in selected:
        expected = coefficient(args.species, args.fermions, tuple(-x for x in w))
        assert value(0, args.fermions, w) == expected
        print(f'theorem {prefix}_c{i} : boundedCoefficient {args.species} {args.fermions} '
              f'{point_text(w)} = {expected} := {names[0, args.fermions, w]}')
else:
    for i, w in selected:
        expected = coefficient(args.species, args.fermions, tuple(-x for x in w))
        print(f'theorem {prefix}_c{i} : boundedCoefficient {args.species} {args.fermions} '
              f'{point_text(w)} = {expected} := by decide +kernel')
if args.index is None and args.chunk is None:
    mult, rank = int(row['multiplicity']), int(row['rank'])
    print(f'theorem {prefix}_assemble (f : SMSparseCharacter.Key → ℤ)')
    for i, w in enumerate(points):
        expected = coefficient(args.species, args.fermions, tuple(-x for x in w))
        print(f'    (h{i} : f {point_text(w)} = {expected})')
    print(f'    : SMCoefficientAssembly.evaluate '
          f'⟨{args.species},{args.fermions},{args.m},({args.delta})⟩ f = ⟨{mult},{rank}⟩ := by')
    print('  unfold SMCoefficientAssembly.evaluate')

    def term(i):
        return f'f {point_text(points[i])}'

    expressions = []
    for color in range(6):
        base = 8*color
        diffs = [f'({term(base+j)} - {term(base+j+1)})' for j in (0, 2, 4, 6)]
        expressions.append(f'({diffs[0]} - {diffs[1]} - ({diffs[2]} - {diffs[3]}))')
    expression = (f'{expressions[0]} - {expressions[1]} - {expressions[2]} + '
                  f'{expressions[3]} + {expressions[4]} - {expressions[5]}')
    print(f'  change Result.mk ({expression}) (columnsFast {args.species} {args.fermions} '
          f'{args.m} - ({expression}).toNat) = _')
    print('  simp only [' + ','.join(f'h{i}' for i in range(48)) + ']')
    print('  decide +kernel')
    print(f'theorem {prefix}_evaluation : solveBounded '
          f'⟨{args.species},{args.fermions},{args.m},({args.delta})⟩ = ⟨{mult},{rank}⟩ :=')
    print(f'  (SMCoefficientAssembly.factor _).trans '
          f'({prefix}_assemble (boundedCoefficient {args.species} {args.fermions})')
    print('    ' + ' '.join(f'{prefix}_c{i}' for i in range(48)) + ')')
    print(f'theorem {prefix}_original : solve '
          f'⟨{args.species},{args.fermions},{args.m},({args.delta})⟩ = ⟨{mult},{rank}⟩ :=')
    print(f'  (solveBounded_eq _).symm.trans {prefix}_evaluation')
print('end GUT.SMNeutralCoefficientCertificate')
