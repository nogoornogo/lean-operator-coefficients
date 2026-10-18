#!/usr/bin/env python3
"""Generate independent 107-row kernel certificates using existing filters/witnesses.

Candidates only: generation never certifies a value. The CSV is not a premise.
Positive witnesses fix occupations; zeros use the proved weak-capacity theorem.
"""
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def main():
    helpers = runpy.run_path(str(HERE/'check-remaining.py'), run_name='verification_helpers')
    rows, _ = helpers['domain']()
    print('import Physics.StandardModel.Operators.SMCompactSupportDecision')
    print('import Physics.StandardModel.Operators.SMConstantWeakCapacity')
    print('import Physics.StandardModel.Operators.SMChiralitySupport')
    print('import Lean.Util.CollectAxioms')
    for name in ['negative-filter-bridge.lean.txt', 'occupation-witness-bridge.lean.txt']:
        text = (HERE/'probes'/name).read_text()
        print('\n'.join(line for line in text.splitlines() if not line.startswith('import ')))
    print('attribute [local instance] SMCompactSupportDecision.contentDecision')
    for index, row in enumerate(rows):
        s, n, m, delta = helpers['key'](row)
        positive = int(row['multiplicity']) > 0
        prop = f'SMJointContentSupport.Supports (fun t => if t = {s} then {n} else 0) {m}'
        claim = prop if positive else '¬ ('+prop+')'
        print(f'\ntheorem certificate_{index} : {claim} := by')
        if not positive:
            print(f'  apply constantWeakCutoff {s} {n} {m} ({delta})')
            print('  · decide +kernel')
            print('  · simp only [SMConstantWeakCapacity.bound, SMConstantWeakCapacity.dimension_eq]')
            print('    decide +kernel')
        elif s in (0, 5) and n in (12, 18, 24):
            a, b = (0, 6) if n == 12 else (6, 6)
            print('  apply (SMJointContentSupport.supports_iff_choices _ _).mpr')
            print(f'  refine ⟨constantOccupationChoice {s} {n} {a} {b} (by decide) (by decide), ?_⟩')
            print('  refine ⟨firstBranch _ (by decide +kernel), ?_⟩')
            print('  decide +kernel')
        else:
            print('  decide +kernel')
        print(f'#check certificate_{index}')
    print('''
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "certificate {name} uses unexpected axiom {ax}"
      count := count+1
  Lean.logInfo m!"neutral certificates: {count} strict transitive checks passed"
''')


if __name__ == '__main__':
    main()
