# Literature And Library Inspection

No external physical theorem or completeness premise is introduced.

- D. Tong, *Electromagnetism*, chapter PDF
  [Electromagnetism and Relativity](https://www.damtp.cam.ac.uk/user/tong/em/em4.pdf),
  reached through the author's Cambridge lecture page. The currently served
  file numbers this chapter 5. Selected text inspected: metric/index rules in
  Sections 5.1.3–5.1.4, field-strength antisymmetry and tensor transformation in
  Section 5.3.2, and the covariant Maxwell equations in Section 5.4. This guides
  conventions, not a claim of a paper-wide or analytic formalization.
- The [parent sources](../derivative-ibp/references.md) and
  [linear-equation register](../linear-eom-weyl/references.md) retain their
  EOM/IBP, ordinary-derivative and source/dual inspection limits.

## Existing Lean Sources

The pinned Physlib `Electromagnetism.ThreeDimension.MaxwellEquations` source
was inspected. Its pointwise electric/magnetic equations use an electromagnetic
potential, smoothness and an extremality condition. That is a different domain
from the present polynomial jet-generator quotient; no equivalence is assumed.
The pinned `GaugeBoson.Realization.FieldStrength` source was inspected for its
formal derivative-symbol field strength, commutator and antisymmetry interface.
Its general gauge realization is not imported as a local completeness premise,
and the non-Abelian closure is not part of this endpoint.

The implementation reuses the repository's actual
[Pauli vector/direction action](../../../Physics/FieldTheory/Jets/LorentzDirections.lean),
[linear equation closure](../../../Math/Algebra/LinearJetEquation.lean),
[actual mixed quotient algebra](../../../Math/Algebra/LinearJetAlgebra.lean),
[kernel theorem](../../../Math/Algebra/LinearJetKernel.lean) and
[EOM/IBP comparison](../../../Math/RepresentationTheory/LinearJetIBP.lean).
Mathlib tensor-product bases, finite sums and quotient linear algebra were
inspected locally. Source inspection remains separate from successful builds
and strict audits; the final implementation roles are recorded below.

## Final Source Roles

The tensor-basis transport, metric polarization, canonical contraction, three
seed intertwiners, full relation closure and transverse probes are local proofs.
Mathlib supplies the tensor and quotient interfaces. The repository's common
linear equation and mixed kernel theorems supply their already proved generic
implications; this physical consumer discharges actual seed covariance. The
existing even derivation and image-grade divergence interfaces supply formal
IBP transport. The final source register is reconciled in
[RELATED_LITERATURE](../../proof/RELATED_LITERATURE.md) before any integration.
No dependency pin, attribution or upstream source is changed. No literature
comparison coverage row or Physlib-wide completeness claim is added.
