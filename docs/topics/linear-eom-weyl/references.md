# Sources And Conventions

No external theorem premise is introduced. The source/dual convention and the
actual covariance are proved locally rather than imported from physics prose.

## Literature

- H. K. Dreiner, H. E. Haber and S. P. Martin, *Two-component spinor techniques
  and Feynman rules for quantum field theory and supersymmetry*,
  [arXiv:0812.1594v6](https://arxiv.org/abs/0812.1594v6),
  [fixed-version full text](https://arxiv.org/pdf/0812.1594v6).
  Metadata and selected full-text portions inspected for the first-order free
  equation and sigma/index conventions: Section 2's spinor transformation
  convention, equation (3.1.2) on printed page 24, and Appendix A's metric
  (A.1) on printed page 156. The massive/interaction, Feynman-rule and amplitude results are
  not premises. The repository uses its existing source-vector/dual convention;
  a full equality with the paper's raised/lowered field notation is not claimed.
- The [parent derivative register](../derivative-ibp/references.md) retains the
  inspected scalar EOM/IBP and operator-basis references. They guide the
  separation of equations, divergence relations and physical amplitudes;
  no counting or completeness statement from them is assumed.

## Checked Repository Inputs

- [Scalar equation and descendants](../../../Math/Algebra/JetEquation.lean).
- [Jet directions](../../../Math/Algebra/JetDirections.lean) and
  [combined actions](../../../Math/Algebra/JetCombined.lean).
- [Actual mixed algebra](../../../Math/Algebra/MixedJetAlgebra.lean) and
  [actual source](../../../Math/RepresentationTheory/MixedJetSource.lean).
- [Scalar EOM/IBP comparison](../../../Math/RepresentationTheory/JetEquationComparison.lean).
- [Pauli action](../../../Physics/FieldTheory/Jets/LorentzDirections.lean) and
  [Weyl component convention](../../../Physics/FieldTheory/Jets/LorentzJetIBP.lean).
- [Local finite-group evaluation](../../../Math/RepresentationTheory/LocalSpurionEvaluation.lean).

Mathlib and the pinned Physlib exterior/locally attributed symmetric derivation
interfaces are reused. Installed revisions remain unchanged. The final record
distinguishes inspected API from the built connections below. The source
roles are reconciled into [RELATED_LITERATURE](../../proof/RELATED_LITERATURE.md)
before any later integration. No literature comparison coverage row is added.

## Implementation Reconciliation

The common relation closure and scalar recovery are local proofs. The actual
exterior/symmetric projection uses Mathlib exterior-map surjectivity and
tensor-map surjectivity; the symmetric projection is onto by generator
induction. The pinned Physlib exterior and attributed symmetric derivations
act on the quotient generators, with their commuting/covariant properties
transported through the proved projection. Image grades and EOM/IBP comparison
are local quotient-linear-algebra constructions.

The actual Weyl covariance is proved by Pauli contraction and a first-jet
frame, keeping the source/dual orientation explicit. The equation parameter
carries the dual right-spin action. Explicit seeds, wave consequences and
null-polarization controls are proved; their conditions are not literature
inputs. No full equality with Physlib's Weyl closure or the paper's field-index
dictionary is asserted. Source authorship and licenses remain in the imported
files; pins and the attributed fragment are unchanged.
