# Implemented Interfaces

| Source | Role |
| --- | --- |
| [SpeciesCopySurplus](../../../Math/RepresentationTheory/Decomposition/SpeciesCopySurplus.lean) | Hom-kernel equivalence, surplus survival, actual kernel splitting and indexed family theorem |
| [ExternalCopyFactorization](../../../Math/RepresentationTheory/Decomposition/ExternalCopyFactorization.lean) | Derive residual copy maps from irreducible gauge intertwiners |
| [PhysicalSpeciesCopySurplus](../../../Physics/FieldTheory/Mass/PhysicalSpeciesCopySurplus.lean) | Independent species Realization, actual light ranges and all-mass physical qque theorem |
| [SpeciesSectorPresentation](../../../Physics/FieldTheory/Mass/SpeciesSectorPresentation.lean) | Derive species mass columns, copy maps and all-mass Model from fixed presentations |

The [Math audit](../../../Math/RepresentationTheory/Decomposition/Audit/AuditSpeciesCopySurplus.lean)
and [Physics audit](../../../Physics/FieldTheory/Mass/Audit/AuditPhysicalSpeciesCopySurplus.lean)
are registered with these sources in their respective aggregates.

## Reused Interfaces

| Existing interface | Role |
| --- | --- |
| [SemisimpleSplitting](../../../Math/RepresentationTheory/Decomposition/SemisimpleSplitting.lean) | Retractions for injections into semisimple representations |
| [PhysicalCommonCopyModel](../../../Physics/FieldTheory/Mass/PhysicalCommonCopyModel.lean) | Unchanged Species mass square, actual range action and light embedding |
| [BipartiteNormalForm](../../../Physics/FieldTheory/Mass/BipartiteNormalForm.lean) | NoPairings interface |
| [QqueSpinorExterior](../../../Physics/StandardModel/Operators/QqueSpinorExterior.lean) | Lorentz/exterior coefficient on common split constituents |
| [PhysicalQqueEndpoint](../../../Physics/StandardModel/Operators/PhysicalQqueEndpoint.lean) | Actual-field physical nonzero endpoint |

The [prior model controls](../../../GUT/Common/ProtonProtection/ModelControls.lean)
remain applications, not imports of the new shared mathematics or physics.
No model-specific scalar/parity dictionary is a universal theorem premise.
New concrete UV adapters remain separate GUT-owned work with checked dictionaries.
See the [result](result.md) for the remaining application conditions.
