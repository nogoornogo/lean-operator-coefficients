#!/usr/bin/env python3
"""Render the committed finite lepton-charge witness module (no proof oracle).

stdout is proposed Lean source, kernel checked by the ordinary module build.
Uses the retained 23 families and fourteen explicit capacity-respecting extras.
"""
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
original = runpy.run_path(str(HERE/'assignment-certificates.py'))


def family(target, z):
    a = abs(z)
    if a < 12:
        return original['family'](target, z)
    c = [0]*10
    c[3 if z >= 0 else 8] = 12
    c[4 if z >= 0 else 9] = a-12
    if target == 3 and z > 0:
        c[0], c[1], c[7], delta = 1, a-6, a-8, 1
    elif target == 3:
        c[0], c[2], c[6], delta = 1, a-5, a-7, -1
    elif z >= 0:
        c[1], c[7], delta = a-4, a-10, 0
    else:
        c[2], c[6], delta = a-2, a-8, 0
    assert all(0 <= x <= cap for x, cap in zip(c, [36,18,18,12,6,36,18,18,12,6]))
    assert sum(c[:3])-sum(c[5:8]) == target
    assert sum(c[3:5])-sum(c[8:10]) == z
    assert sum(x*y for x,y in zip(c, [1,4,-2,-3,-6,-1,-4,2,3,6]))+3*delta == 0
    return c, delta


def generate():
    print('''import Physics.StandardModel.Operators.Support.Decomposition.SMCompactSupportDecision
import Physics.StandardModel.Operators.Support.Dimension.SMChargeDegreeBounds

/-! Explicit full joint-support witnesses for every capacity/parity candidate
lepton charge at B3=3 or 6. Rendered by finite-charge-witnesses.py; every
declaration is checked by the normal library build. No CSV/table premise. -/
-- Elaborate the generated certificates sequentially within this module.
set_option Elab.async false

namespace Physics.SMLeptonChargeWitnesses
open Math Physics
''')
    helper = (HERE/'probes/occupation-witness-bridge.lean.txt').read_text()
    print('\n'.join(line.replace('open Math GUT', 'open Math Physics')
                    for line in helper.splitlines() if not line.startswith('import ')))
    print('''noncomputable def balanced (c : DeltaLOneSignedInput.Species → Nat) :
    GenerationTensorSupport.Choice (SMJointContentSupport.tree c) := by
  apply indexedOccupationChoice 9 (SMJointContentSupport.leaves c)
  intro t
  exact pickOccupation (c t) (c t / 3) ((c t + 1) / 3) (by omega) (by omega)
''')
    emit = original['emit_family']
    emit.__globals__['family'] = family
    for target, zs in [(3, range(-17,18,2)), (6, range(-18,19,2))]:
        for z in zs:
            emit(target, z)
            tag = original['name'](target,z)
            c, delta = family(target,z)
            n, m = sum(c), abs(delta)
            h, d = max(delta,0), max(-delta,0)
            print(f'''theorem {tag}_charges : SMQLPatternRequests.blCharge {tag}_pattern = ({target},{z}) := by
  decide +kernel

theorem {tag}_neutral {{k : Nat}} [NeZero k] (q l : ZMod k)
    (hc : ({target} : ZMod k)*q + ({z} : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs={target}) := by
  apply {tag}_allowed
  rw [SMChargeDegreeBounds.residual_linear, {tag}_charges]
  simpa using hc

theorem {tag}_exact {{k : Nat}} [NeZero k] (q l : ZMod k)
    (hc : ({target} : ZMod k)*q + ({z} : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=({target},{z})) := by
  refine ⟨{n}, {tag}_pattern, {h}, {d}, {tag}_charges, ?_⟩
  apply (SMJointHiggsSupport.original_ql_iff {tag}_pattern q l {h} {d}).mpr
  refine ⟨?_, by decide +kernel, ⟨⟨{m}, by decide +kernel⟩, ?_, ?_⟩⟩
  · rw [SMChargeDegreeBounds.residual_linear, {tag}_charges]
    simpa using hc
  · change BoundedHiggsSupport.Admissible {h} {d} {m}
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [{tag}_counts_eq]
    exact {tag}_support
''')
    print('end Physics.SMLeptonChargeWitnesses')


if __name__ == '__main__':
    generate()
