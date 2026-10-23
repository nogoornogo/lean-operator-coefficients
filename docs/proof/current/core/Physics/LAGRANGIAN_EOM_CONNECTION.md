# Lagrangian To EOM Connection

The [result](../../../../topics/formal-first-variation/results.md) records the
normalizations, boundary currents and precise algebraic scope; see also
[verification](../../../../topics/formal-first-variation/verification.md).

`Physics.ScalarFirstVariation` derives the interacting scalar seed from its
normalized kinetic/quartic density. `Physics.YangMillsFirstVariation` derives the
existing formal matrix equations from the trace curvature-square density.
Both use actual evolutionary derivations on full off-shell jets, admit
arbitrary polynomial variations, prove the actual substitution coefficient,
and descend to ordinary IBP and full EOM/IBP sources.

The matrix component dual is transposed and carries the signature sign.
Explicit component extraction and equality of differential ideals prove
agreement including every descendant. The generic EOM-input API is unchanged.
No integrated action, analytic boundary hypothesis or quantum equivalence
is asserted. `Physics.FieldTheory.Jets.Scalar.Inputs.Audit.AuditFirstVariation` checks all
31 public declarations transitively and rejects model-layer imports.
