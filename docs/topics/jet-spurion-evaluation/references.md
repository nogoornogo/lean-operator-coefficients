# Sources And Connection Roles

No external theorem premise is introduced. This topic composes independently
proved repository results; it does not certify a paper-wide saturation theorem.

## Literature Guidance

- Grinstein, Lu, Miró and Quílez, *Most general EFTs from spurion analysis:
  Hilbert series and Minimal Lepton Flavor Violation*,
  [arXiv:2412.16285v1](https://arxiv.org/abs/2412.16285v1).
  The [finite-group register](../finite-group-spurion-evaluation/references.md)
  owns the inspected locations and conditions. The generic-VEV/general-group
  claims are not imported here. The local finite-group result applies at
  every value, with its own proved finite interpolation bound.
- Henning, Lu, Melia and Murayama, *Operator bases, S-matrices, and their
  partition functions*, [arXiv:1706.08520v1](https://arxiv.org/abs/1706.08520v1).
  The [derivative register](../derivative-ibp/references.md) owns the earlier
  inspection. It guides the separation of EOM, IBP and physical interpretation;
  no amplitude, counting or variational theorem is a premise.
- Brion's covariant-module background and its unverified general-group bridge
  stay at the [earlier boundary](../all-degree-symmetry-protection/feasibility.md).
  No geometric foundation is reopened in this connection.

## Actual Repository Inputs

- [Finite-group coefficient evaluation](../../../Math/RepresentationTheory/FiniteGroupSpurionCoefficients.lean)
  and [degree bounds](../../../Math/RepresentationTheory/FiniteGroupSpurionDegree.lean).
- [Local coinvariant coefficients](../../../Math/RepresentationTheory/LocalCoinvariantHom.lean):
  locally constructed quotient; no new identification with Mathlib coinvariants.
- [Actual direction IBP](../../../Math/RepresentationTheory/DirectionalJetIBP.lean),
  [scalar EOM/IBP actions](../../../Math/RepresentationTheory/JetEquationComparison.lean)
  and [mixed source](../../../Math/RepresentationTheory/MixedJetSource.lean).
- [Complete mixed quotient](../../../Math/Algebra/MixedJetQuadratic.lean) and
  [Lorentz wave symbol](../../../Physics/FieldTheory/Jets/LorentzDirections.lean).

The installed dependency revisions are unchanged. Existing Mathlib, TauCeti
and Physlib source attributions stay in the parent registers. Record which
interfaces are instantiated and audited in the final result; do not describe
source inspection or a conditional generic bridge as a proved physical model.

## Implementation Reconciliation

[LocalSpurionEvaluation](../../../Math/RepresentationTheory/LocalSpurionEvaluation.lean)
composes the local quotient and existing bounded coefficient evaluation with
both inverse formulas. [JetSpurionEvaluation](../../../Math/RepresentationTheory/JetSpurionEvaluation.lean)
constructs the actual product actions, proves mixed relation stability and
connects scalar off-shell and mixed tensor representatives. The
[physical consumer](../../../Physics/FieldTheory/Jets/LorentzSpurionEvaluation.lean)
uses the existing proved wave-symbol invariance, not an inspected upstream API.
The [complete example](../../../Math/Algebra/MixedJetSpurionExample.lean)
derives its entire sign action from actual component actions and the previously
proved mixed quotient. No basis-completeness or external covariance premise
is substituted for these connections.

[RELATED_LITERATURE](../../proof/RELATED_LITERATURE.md) now records these final
source roles, preserving finite-group, constant-spurion and fixed-grade
conditions. The Math and Physics assumption ledgers link the same result.
No new literature-comparison coverage row is added: neither paper-wide
saturation nor amplitude/counting equivalence has been compared or certified.
