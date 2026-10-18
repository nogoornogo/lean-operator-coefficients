# Limited Audit Results

## Decision

Proceed with the limited qque operator milestone. No counterexample, new
generation bound, or new physical source assumption was found. This is a
feasibility decision backed by small Lean lemmas and a finite exact computation,
**not** the completed Lorentz/SM/H operator theorem on actual light fields.

| Question | Finding | Evidence and limit |
| --- | --- | --- |
| Required Q-exchange symmetry under current inputs? | Yes, by reconstructing with one shared Q projection | Lean proves an H-invariant symmetric nonzero coefficient from three split maps to the same nonzero representation. The existing compact source supplies these maps; the full field assembly is not implemented here |
| One generation survives antisymmetry? | Yes in the explicit component test | Lean checks the selected exterior expression and its determinant detector value 2. Integer computation checks the full one-generation expansion. Its identity with a general source-derived operator is not yet a Lean theorem |
| Do existing exterior APIs suffice? | Yes for the inspected descent/nonvanishing/transport route | The universal property is exercised by the Lean detector. Full equivariance and field assembly remain implementation work |

## Exchange Symmetry

The standard qque contraction uses color, weak, left-spinor and right-spinor
epsilons. Exchanging the complete two Q components reverses color, weak and
left-spinor signs, so their product changes sign. Fermionic exchange supplies
the other minus sign. The required flavor coefficient is **symmetric**, not
antisymmetric, in the Q slots. This agrees with Alonso et al.,
[Eq. (1) and Eq. (9)](https://arxiv.org/html/1405.0486v2). No implementation
from that source was copied into Lean.

An arbitrary nonzero ordered coefficient need not survive. Instead, use ONE
Q representation A and split projection p : A -> R, with the existing up/e
dual projections into R*. Construct

```text
F(x,y,u,e) = u'(p(x)) e'(p(y)) + u'(p(y)) e'(p(x)).
```

The [Lean probe](../../../Physics/StandardModel/Operators/Audit/AuditQqueStatisticsFeasibility.lean)
proves H-equivariance, Q symmetry and nonvanishing. Choose nonzero r and a
dual phi with phi(r)=1; both Q slots use the same lifted r and both dual slots
use the lifted phi. The result is 2. Nonzero R suffices, with no dimension >= 2
assumption, and H can be any group in this algebraic lemma.

Connection to current inputs, established by source inspection:

- `CompactLightQque.common_quotient` already derives a nonzero R and split
  maps from L_0, L_3, L_8, L_14. Use the L_0 split twice, plus L_8 and L_14.
- `CompactExplicitSMTensor.Decomposition.quark0` identifies the actual Q
  field with Q_SM tensor L_0. Use that same equivalence twice; distinct
  `quark3` coordinates need not be used in the new construction.
- The existing up/e identifications supply the contragredient factors.

Thus independently chosen Q projections in the old proof need not agree.
The new coefficient need not equal its old existential witness. No new
requirement that an ambient conjugator preserve the radical is introduced.

## One Generation

Choose distinct components of ONE generation:

```text
Q_(color0,weak0,left0), Q_(color1,weak1,left1),
u_(color2,right0), e_right1.
```

Setting all other components to zero leaves two Q orderings, with contractions
+1 and -1. For their four Grassmann generators the expression is

```text
theta_0 theta_1 theta_2 theta_3 - theta_1 theta_0 theta_2 theta_3
= 2 theta_0 theta_1 theta_2 theta_3 != 0.
```

Lean checks the scalar signs, their agreement with this two-term expression,
and nonvanishing in the fourth exterior power of C^4 via a determinant
functional taking value 2. A negative control with a repeated component
vanishes. These are component labels, not four generations.

The independent [integer cross-check](../../../tools/qque/audit_one_generation.py)
expands all 48 nonzero epsilon-index contributions on 12 Q, 6 up-right and 2
electron-right components. Grassmann sorting leaves 24 monomials with
coefficients +2 or -2. Projection to the four selected components gives the
expression tested in Lean. This script is not a trusted Lean oracle or a UV
model. A nonzero normalization factor does not affect this test.

## API Assessment

Pinned mathlib already provides the required exterior infrastructure:

- `MultilinearMap.alternatization`: alternating a multilinear coefficient.
- `exteriorPower.ιMulti`: fixed-degree wedge.
- `exteriorPower.alternatingMapLinearEquiv` and
  `alternatingMapLinearEquiv_apply_ιMulti`: descent and evaluation. The probe
  uses these directly, rather than assuming a quotient exists.
- `exteriorPower.map` and `map_apply_ιMulti`: transport along field maps.
- `AlternatingMap.map_eq_zero_of_eq`: repeated-component negative control.
- `ExteriorAlgebra.liftAlternating`: an all-degree alternative; the fixed-degree
  interface is sufficient and better bounded for this task.

`SMEpsilonTensor.eps2_invariant` already handles any determinant-one complex
2x2 matrix, not just SU(2). The probe reuses it for a spinor epsilon. Explicit
left/right spinor representations and the SL(2,C) conjugation convention
remain to be assembled. This audit does not identify a Lorentz group or prove
its covering theorem. No dependency upgrade or new exterior foundation is
needed for the inspected algebraic route.

## Remaining Work

1. Define the Weyl-spinor actions and invariant pairings with a fixed
   Lorentz-cover convention; do not develop general Lorentz geometry.
2. Combine residual, gauge and spinor factors into a degree-(2Q,1u,1e)
   alternating coefficient on the direct sum of fields. Prove nonvanishing
   and simultaneous SM/H/spinor-cover invariance.
3. Transport to actual light subrepresentations with the existing explicit
   SM decomposition; audit dual directions and hypotheses.

Distinguish a functional on the fourth exterior power of the field space
from an exterior coefficient on its dual. Any equivalence used between them
must be supplied, not silently assumed.

The earlier 2-6 week implementation estimate remains conservative, but two
uncertainties have narrowed: one generation does not force vanishing, and
the needed exterior foundation exists. These probes do not measure the cost
of assembling the full actual-field endpoint. No anomaly, Wilson coefficient,
decay amplitude or lifetime claim is added.

Verification and integration: [topic record](README.md).
