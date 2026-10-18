# Arbitrary Mixed-Power Descent Checkpoint

`SymmetricPowerDescent.equiv` proves the universal-property inverse for any
boson degree, including zero. `MixedPowerDescent.orderedEquiv` composes this
with tensor currying and exterior-power descent for arbitrary n,m. Its
`equivariantEquiv` connects the actual mixed representation to ordered maps
with alternating fermions, symmetric bosons and group equivariance.

`LocalExchangeHom.equiv` transports signed exchange constraints through local
coinvariant descent and realizes the constrained coefficients as Hom from an
explicit successive quotient. The generator formula proves compatibility of
the two extraction maps. No local spanning dictionary is assumed.

Regression theorems cover the two-boson inverse, boson exchange and repeated
fermion vanishing. The focused audit passes 13 strict transitive checks (3,179
jobs); full build passes (6,492 jobs). Local layout/link/diff checks accompany
the checkpoint. This is not the entire milestone B: species-support projection,
typed content assembly and local/flavor regrouping still require connection.
Grading and the final SM consumers also remain open.

- [Symmetric descent](../../../Math/RepresentationTheory/SymmetricPowerDescent.lean)
- [Mixed descent](../../../Math/RepresentationTheory/MixedPowerDescent.lean)
- [Local/exchange descent](../../../Math/RepresentationTheory/LocalExchangeHom.lean)
- [Audit and regressions](../../../Math/RepresentationTheory/Audit/AuditMixedPowerDescent.lean)
