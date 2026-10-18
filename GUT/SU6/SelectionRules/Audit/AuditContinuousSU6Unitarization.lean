import GUT.SU6.Representations.ContinuousSU6Unitarization

/-!
# Axiom audit for full SU(6) unitarization

This audit covers the analytic bridge from an arbitrary finite-dimensional
complex `SU(6)` representation with a jointly continuous action and a seed
Hermitian norm to an equivalent continuous unitary representation.  It also
checks the locally supplied compactness proof for the concrete matrix group
`SU(6)`.

This construction changes the Hilbert norm but not the algebraic
representation.  It does not construct a representation from a Lagrangian or
establish the Standard Model chiral-index hypothesis.
-/

#print axioms GUT.ContinuousSU6Unitarization.unitaryMatrix_entry_norm_le_one
#print axioms GUT.ContinuousSU6Unitarization.specialUnitaryGroup_isClosed
#print axioms GUT.ContinuousSU6Unitarization.specialUnitaryGroup_isBounded
#print axioms GUT.ContinuousSU6Unitarization.specialUnitaryGroup_isCompact
#print axioms GUT.ContinuousSU6Unitarization.HaarSU6Copy.jointlyContinuous
#print axioms GUT.ContinuousSU6Unitarization.HaarSU6Copy.unitary
#print axioms GUT.ContinuousSU6Unitarization.model
#print axioms GUT.ContinuousSU6Unitarization.modelEquiv
#print axioms GUT.ContinuousSU6Unitarization.ofContinuous
#print axioms GUT.ContinuousSU6Unitarization.ofContinuousEquiv
