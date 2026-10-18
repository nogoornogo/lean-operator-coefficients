#!/usr/bin/env python3
"""Emit a closed Lean verification target; CSV values are candidates, not premises."""
import argparse
import csv
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('species', type=int)
parser.add_argument('fermions', type=int)
parser.add_argument('m', type=int)
parser.add_argument('delta', type=int)
parser.add_argument('--backend', choices=('direct', 'grouped', 'bounded'), default='direct')
args = parser.parse_args()
key = args.species, args.fermions, args.m, args.delta
with Path(__file__).with_name('neutral-sparse-results.csv').open(newline='') as inp:
    matches = [row for row in csv.DictReader(inp)
               if tuple(int(row[k]) for k in ('species', 'fermions', 'm', 'delta')) == key]
if len(matches) != 1:
    parser.error('expected exactly one row in the bounded 107-row candidate output')
row = matches[0]
value, rank = int(row['multiplicity']), int(row['rank'])
if args.backend == 'direct':
    print('import Physics.StandardModel.Operators.SMNeutralSparseRanks')
    solver = 'solveDirectWith SMKernelWeightData.tables'
else:
    print('import Physics.StandardModel.Operators.SMGroupedCharacter')
    solver = 'SMGroupedCharacter.' + ('solveGrouped' if args.backend == 'grouped' else 'solveBounded')
print('open GUT SMNeutralSparseRanks')
print('/- Candidate output becomes a theorem only after kernel verification succeeds. -/')
print(f'example : {solver} '
      f'⟨{args.species},{args.fermions},{args.m},({args.delta})⟩ = '
      f'⟨{value},{rank}⟩ := by decide +kernel')
