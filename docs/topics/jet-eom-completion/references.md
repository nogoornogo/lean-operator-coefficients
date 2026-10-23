# Sources And Implementation Roles

No literature theorem is imported as a premise. Conventions are inherited from
the [preceding source register](../linear-eom-weyl/references.md), including its
selected full-text inspection and its explicit source-vector/dual boundary.

- H. K. Dreiner, H. E. Haber and S. P. Martin,
  *Two-component spinor techniques and Feynman rules for quantum field theory
  and supersymmetry*, [0812.1594v6](https://arxiv.org/abs/0812.1594v6).
  The bibliographic page and abstract were checked again for this extension.
  The prior selected reading covers Section 2, equation (3.1.2) and Appendix A;
  no new paper-wide or classical field-index comparison is claimed. The right
  equation, conjugate representation and product-order reversal are proved
  in the repository's fixed algebraic source convention.
- B. Henning, X. Lu, T. Melia and H. Murayama,
  *Operator bases, S-matrices, and their partition functions*,
  [1706.08520v1](https://arxiv.org/abs/1706.08520v1).
  Abstract and metadata checked for the EOM/IBP framework. The inherited
  derivative survey retains its separate inspection limits. The null consumer
  does not certify a Hilbert-series, momentum-space or amplitude comparison.

## Checked Lean Inputs

- [Actual mixed projection](../../../Math/Algebra/LinearJetAlgebra.lean) and
  [image-grade divergence comparison](../../../Math/RepresentationTheory/LinearJetIBP.lean).
- [Existing exterior adjoint](../../../Math/LinearAlgebra/ExteriorHermitianConjugation.lean):
  conjugate scalar twist followed by order reversal, rather than replacing
  Mathlib's scalar-fixed Clifford star globally.
- [Existing Pauli and real direction convention](../../../Physics/FieldTheory/Jets/LorentzDirections.lean)
  and [Weyl component actions](../../../Physics/FieldTheory/Spinor/WeylSpinor.lean).
- [Existing left equations and probes](../../../Physics/FieldTheory/Jets/WeylEquationControls.lean).

Installed Mathlib source was inspected for `TwoSidedIdeal.span`, kernels and
ring-congruence quotients; projective linear splitting; free exterior/symmetric
maps; Finsupp weight/predecessor lemmas; semilinear map and submodule quotient
interfaces. The final proofs use these APIs with persistent transitive audits.
Pinned Physlib supplies the existing even exterior derivation. No upstream
source is edited, and dependency pins and attribution remain unchanged.

The general closure, mixed ideal identity, complete null example and actual
right-Weyl/adjoint connections are local proofs. The final roles are also
reconciled in [RELATED_LITERATURE](../../proof/RELATED_LITERATURE.md). This is
source maintenance, not a new literature comparison coverage claim.
