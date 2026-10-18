#!/usr/bin/env python3
"""Propose closed Lean proofs for all 572 existing assignments; no table premise.

Default: generated Lean to stdout. --csv: proposed partition. Kernel-check the
Lean output before interpreting any proposed verdict as certified.
"""
import argparse
import csv
import math
from pathlib import Path
import runpy
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def domain():
    mod = runpy.run_path(str(ROOT/'tools/sm-rank-enumeration/enumerate.py'))
    rows = mod['enumerate_candidates']()
    mod['report'](rows)
    with (ROOT/'tools/sm-rank-enumeration/candidates.csv').open(newline='') as f:
        assert list(csv.DictReader(f)) == [{k: str(v) for k, v in r.items()} for r in rows]
    return rows


def partition():
    result = []
    for row in domain():
        k, q, l = (row[t] for t in ('k', 'q', 'l'))
        # Infinite congruence solvability, not a bounded lepton search.
        b1 = (3*q+l) % math.gcd(2*l, k) != 0
        possible = [z for z in range(-11, 12, 2) if (3*q+z*l) % k == 0]
        assert b1 == (not possible)
        z = None if b1 else min(possible, key=lambda x: (abs(x), x))
        b2 = (6*q) % math.gcd(2*l, k) != 0
        possible2 = [z for z in range(-10, 11, 2) if (6*q+z*l) % k == 0]
        assert b2 == (not possible2)
        b2z = None if b2 else min(possible2, key=lambda x: (abs(x), x))
        result.append(dict(k=k, q=q, l=l, b1_forbidden=b1,
            b1_witness_L='' if z is None else z,
            b2_forbidden=b2,
            b2_witness_L='' if b2z is None else b2z,
            b1_forbidden_b2_allowed=b1 and not b2))
    assert len(result) == 572
    assert sum(r['b1_forbidden'] for r in result) == 246
    assert sum(r['b1_forbidden_b2_allowed'] for r in result) == 144
    assert sum(r['b2_forbidden'] is True for r in result) == 102
    # Independent periodic arithmetic and unit-orbit regression controls.
    lookup = {(r['k'], r['q'], r['l']): r for r in result}
    for r in result:
        k, q, l = (r[t] for t in ('k', 'q', 'l'))
        for target, key in [(3, 'b1'), (6, 'b2')]:
            excluded = not any((target*q+z*l) % k == 0
                               for z in range(2*k) if (target+z) % 2 == 0)
            assert excluded == r[key+'_forbidden']
        for u in range(k):
            if math.gcd(u, k) == 1:
                other = lookup[k, u*q % k, u*l % k]
                assert all(r[key] == other[key] for key in
                           ['b1_forbidden', 'b2_forbidden', 'b1_forbidden_b2_allowed'])
    return result


def family(target, z):
    if target == 3:
        a = abs(z)
        if z > 0:
            t = 2*((a-1)//4)
            c = [3,t,0,a,0,0,0,t,0,0]
            delta = a-1-2*t
        else:
            t = 2*((a+1)//4)
            c = [0,1,2+t,0,0,0,t,0,a,0]
            delta = 2*t-a
    elif z >= 0:
        t = 2*max(0, (z-2)//4)
        c = [6,t,0,z,0,0,0,t,0,0]
        delta = z-2-2*t
    else:
        a = -z
        t = 2*(a//4)
        c = [0,2,4+t,0,0,0,t,0,a,0]
        delta = 2*t-a
    assert all(0 <= x <= cap for x, cap in zip(c, [36,18,18,12,6,36,18,18,12,6]))
    assert sum(c[:3])-sum(c[5:8]) == target
    assert sum(c[3:5])-sum(c[8:10]) == z
    weights = [1,4,-2,-3,-6,-1,-4,2,3,6]
    assert sum(x*y for x,y in zip(c, weights))+3*delta == 0
    return c, delta


def name(target, z):
    return f'w{target}_{"p" if z >= 0 else "n"}{abs(z)}'


def emit_family(target, z):
    tag = name(target, z)
    c, delta = family(target, z)
    n, m = sum(c), abs(delta)
    h, d = max(delta, 0), max(-delta, 0)
    terms = []
    end = 0
    for s, count in enumerate(c):
        if count:
            end += count
            terms.append(f'if i.val < {end} then {s} else ')
    pat = ''.join(terms)+'0'
    print(f'def {tag}_counts : DeltaLOneSignedInput.Species → Nat := ![{",".join(map(str,c))}]')
    print(f'def {tag}_pattern (i : Fin {n}) : DeltaLOneSignedInput.Species := {pat}')
    print(f'''theorem {tag}_counts_eq : SMIteratedContent.counts {tag}_pattern = {tag}_counts := by
  funext s
  fin_cases s <;> decide +kernel

theorem {tag}_support : SMJointContentSupport.Supports {tag}_counts {m} := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨balanced {tag}_counts, firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem {tag}_allowed {{k : Nat}} [NeZero k] (q l : ZMod k)
    (hc : QLFiniteSupport.charge q l {tag}_pattern=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs={target}) := by
  refine ⟨{n}, {tag}_pattern, {h}, {d}, by decide +kernel, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff {tag}_pattern q l {h} {d}).mpr
  refine ⟨hc, by decide +kernel, ⟨⟨{m}, by decide +kernel⟩, by change BoundedHiggsSupport.Admissible {h} {d} {m}; unfold BoundedHiggsSupport.Admissible; omega, ?_⟩⟩
  rw [{tag}_counts_eq]
  exact {tag}_support
''')


def exclusion(k, q, l, target):
    print(f'''  apply parityExclusion {k} {q} {l} {target}
  intro b z hb he
  have hab := Int.natAbs_eq_iff.mp hb
  rcases hab with hb | hb <;> omega''')


def generate(rows):
    print('import Physics.StandardModel.Operators.SMCompactSupportDecision')
    print('import Lean.Util.CollectAxioms')
    for filename in ['assignment-parity-bridge.lean.txt', 'occupation-witness-bridge.lean.txt']:
        text = (HERE/'probes'/filename).read_text()
        # Imports must precede declarations, so repeat their union explicitly.
        if filename == 'assignment-parity-bridge.lean.txt':
            print(text)
        else:
            print('\n'.join(s for s in text.splitlines() if not s.startswith('import ')))
    print('''noncomputable def balanced (c : DeltaLOneSignedInput.Species → Nat) :
    GenerationTensorSupport.Choice (SMJointContentSupport.tree c) := by
  apply indexedOccupationChoice 9 (SMJointContentSupport.leaves c)
  intro t
  exact pickOccupation (c t) (c t / 3) ((c t + 1) / 3) (by omega) (by omega)
''')
    for z in range(-11, 12, 2):
        emit_family(3, z)
    for z in range(-10, 11, 2):
        emit_family(6, z)
    print('''theorem allowed_not_forbidden {k : Nat} [NeZero k] (q l : ZMod k)
    (select : Int × Int → Prop)
    (ha : SMQLPatternRequests.OriginalAllowed q l select) :
    ¬ SMQLPatternRequests.OriginalForbidden q l select := by
  obtain ⟨n,p,h,d,hs,ha⟩ := ha
  intro hf
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp (hf n p h d hs) ha
''')
    for i, row in enumerate(rows):
        k, q, l = (row[t] for t in ('k', 'q', 'l'))
        prefix = f'a{i}'
        vals = f'({q} : ZMod {k}) {l}'
        for target, key in [(3, 'b1'), (6, 'b2')]:
            forbidden = row[key+'_forbidden']
            prop = 'OriginalForbidden' if forbidden else 'OriginalAllowed'
            print(f'theorem {prefix}_{key} : SMQLPatternRequests.{prop} {vals} (fun c => c.1.natAbs={target}) := by')
            if forbidden:
                exclusion(k, q, l, target)
            else:
                tag = name(target, row[key+'_witness_L'])
                print(f'  apply {tag}_allowed\n  decide +kernel')
        accepted = row['b1_forbidden_b2_allowed']
        print(f'theorem {prefix}_request : {"" if accepted else "¬ "}SMQLPatternRequests.Satisfies {vals} SMQLPatternRequests.b1ForbiddenB2Allowed := by')
        if accepted:
            print(f'  exact (SMQLPatternRequests.b1_b2_original_iff _ _).mpr ⟨{prefix}_b1, {prefix}_b2⟩')
        elif not row['b1_forbidden']:
            print(f'  intro h\n  exact allowed_not_forbidden _ _ _ {prefix}_b1 ((SMQLPatternRequests.b1_b2_original_iff _ _).mp h).1')
        else:
            print(f'  intro h\n  exact allowed_not_forbidden _ _ _ ((SMQLPatternRequests.b1_b2_original_iff _ _).mp h).2 {prefix}_b2')
    print('''run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "assignment certificate {name} uses unexpected axiom {ax}"
      count := count+1
  Lean.logInfo m!"572 assignment certificates: {count} strict transitive checks passed"
''')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--csv', action='store_true')
    args = parser.parse_args()
    rows = partition()
    if args.csv:
        writer = csv.DictWriter(sys.stdout, fieldnames=list(rows[0]), lineterminator='\n')
        writer.writeheader()
        writer.writerows(rows)
    else:
        generate(rows)
