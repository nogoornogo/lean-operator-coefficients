# Signed One-Higgs Residual Coordinates

## Established Result

`BnvSevenSignedCoordinates.equiv` identifies the entire independent BNV
degree `(4,1)` with eight explicit constrained residual-Hom factors.
The local ranks are `2,2,1,2` for each baryon-number sign. Its
`forbidden_iff` and `nonzero_iff` are two-sided criteria on the actual input,
not criteria conditional on a proposed spanning dictionary.

`BnvSevenNegativeTransport` constructs the negative local dictionaries from
the positive dictionaries using involutive gauge and Weyl group maps.
`BnvSevenNegativeCoordinates` transports actual typed exchange relations
through the proved extraction/reconstruction equivalence. No identification
of opposite residual flavor modules or scalar multiplicities is required.

The reusable `SpecialUnitaryContragredient`, `SMGaugeConjugation`, and
`BnvLocalConjugation` interfaces implement the finite gauge-carrier dual
identifications and chirality reversal. These are complex-linear carrier
maps over a transformed group action, not a conjugation assumption on all
model fields.

## Checkpoint Boundary

This completes the one-Higgs degree, not the whole bounded dimension-seven
gate. The scalar-free degree must still be connected to the full signed
dimension-six residual classification with independent multiplicities;
the lower-degree decomposition, total bounded criterion and controls then
need assembly. Dimensions eight through eleven have not been implemented.

This was the boundary at checkpoint `checkpoint 01`. The
[whole dimension-seven endpoint](../../proof/current/applications/Physics/BNV_SEVEN_COMPLETENESS.md)
now resolves the scalar-free connection, bounded assembly and controls.
Dimensions eight through eleven remain deferred. No master integration is authorized.

## Sources And Verification

- [Signed coordinates](../../../Physics/StandardModel/Operators/BnvSevenSignedCoordinates.lean)
- [Negative coordinates](../../../Physics/StandardModel/Operators/BnvSevenNegativeCoordinates.lean)
- [Negative local transport](../../../Physics/StandardModel/Operators/BnvSevenNegativeTransport.lean)
- [Persistent transitive audit](../../../Physics/StandardModel/Operators/Audit/AuditBnvBoundedSupport.lean)

Focused signed-coordinate build passes. Final checkpoint checks are recorded
in the topic overview. No literature statement is used as a completeness
premise.
