#!/usr/bin/env python3
"""Historical independent all-content degree-certificate cross-check.

The default library now proves all row bounds using SMFiniteLeptonDegreeBounds;
this generator is retained for reproducing the earlier independent certificates.

Uses the same proposed minimal |L|, but proves the arithmetic exclusion for
every smaller integer L, then applies the actual-support degree bridge.
Must be kernel checked including the final strict audit.
"""
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent


def generate():
    rows = runpy.run_path(str(HERE/'assignment-certificates.py'))['partition']()
    print('''import Physics.StandardModel.Operators.SMChargeDegreeBounds
import Lean.Util.CollectAxioms
open Math GUT
namespace AssignmentDegreeCertificates
''')
    count = 0
    for index, row in enumerate(rows):
        k, q, l = (row[t] for t in ('k', 'q', 'l'))
        for b, key in [(3, 'b1'), (6, 'b2')]:
            if row[key+'_forbidden']:
                continue
            lower = abs(row[key+'_witness_L'])
            tag = f'a{index}_{key}'
            print(f'''theorem {tag}_gate (B L : Int) (_hb : B.natAbs={b})
    (_hp : (B+L)%2=0)
    (_hc : (B : ZMod {k})*{q} + (L : ZMod {k})*{l}=0) : {lower} ≤ |L| := by''')
            if lower == 0:
                print('  exact abs_nonneg L')
            else:
                print(f'''  have hc' : (((B*{q}+L*{l}) : Int) : ZMod {k})=0 := by
    push_cast
    exact _hc
  have hz := Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ {k}).mp hc')
  by_contra hn
  obtain ⟨hlo,hhi⟩ := abs_lt.mp (lt_of_not_ge hn)
  rcases Int.natAbs_eq_iff.mp _hb with hb | hb <;> omega''')
            print(f'''
theorem {tag}_lower {{n : Nat}} (p : Fin n → DeltaLOneSignedInput.Species) (h d : Nat)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs={b})
    (ha : SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor ({q} : ZMod {k}) {l}) p h d)) :
    {b+lower} ≤ n ∧ {3*(b+lower)} ≤ SMChargeDegreeBounds.twiceDimension n h d :=
  SMChargeDegreeBounds.original_degree_lower ({q} : ZMod {k}) {l}
    {b} {lower} {tag}_gate p h d hb ha
''')
            count += 1
    print(f'''end AssignmentDegreeCertificates
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "degree certificate {{name}} uses unexpected axiom {{ax}}"
      count := count+1
  Lean.logInfo m!"{count} degree bounds: {{count}} strict transitive checks passed"
''')


if __name__ == '__main__':
    generate()
