# Existing Sections Separated During Relocation

All listed sections retain their original declaration namespaces and proof
bodies. They are moves of existing results, not generalizations or new inputs.

| Source at base `checkpoint 01` | Destination | Section |
| --- | --- | --- |
| `GUT/SU6/Embeddings/CompactEmbeddingClassification.lean` | [UnitaryRepresentation](../../../Math/RepresentationTheory/Unitary/UnitaryRepresentation.lean) | Generic complete reducibility compatibility API |
| `GUT/SU6/Embeddings/ContinuousRepresentationScope.lean` | [ContinuousAction](../../../Math/RepresentationTheory/Unitary/ContinuousAction.lean) | Joint continuity and continuous irreducible scope |
| `GUT/SU6/SelectionRules/FlippedBranch/PhysicalRestrictionBridge.lean` | [VirtualRepresentation](../../../Math/RepresentationTheory/Characters/VirtualRepresentation.lean) | Actual and finite virtual representations of any group |
| `GUT/SU6/Hypercharge/BlockCentralizer.lean` | [Schur](../../../Math/RepresentationTheory/Decomposition/Schur.lean) | General Schur lemmas and surjective restriction |
| `GUT/SU6/Characters/WeightTheory.lean` | [EigenbasisTrace](../../../Math/LinearAlgebra/EigenbasisTrace.lean) | Trace of a diagonal action in a basis |
| `GUT/SU6/Representations/ContinuousUnitaryConstructions.lean` | [ContinuousConstructions](../../../Math/RepresentationTheory/Unitary/ContinuousConstructions.lean) | Generic basis copies and tensor products |
| `GUT/RepresentationTheory/CompactRepresentationUnitarization.lean` | [HaarAveraging](../../../Math/RepresentationTheory/Unitary/HaarAveraging.lean) | Compact-group averaged inner product |
| `GUT/RepresentationTheory/CompactProductFactorization.lean` | [CompactProductClassification](../../../GUT/SU6/Adapters/CompactProductClassification.lean) | SU2/SU3 application separated from the [generic product theorem](../../../Math/RepresentationTheory/Decomposition/CompactProductFactorization.lean) |

The table's source column intentionally records historical paths. The
[whole-file map](../../../tools/layout/source-map.json) describes relocations;
it is not a per-declaration provenance map for split modules.

The first build revealed that the last application section still depended on
the concrete differentiated SU2/SU3 interface. That section was moved to GUT,
not made a dependency of Math. No heartbeat limits or proof assumptions were
increased to work around the missing import.

[AuditExtractedInterfaces](../../../Math/Audit/AuditExtractedInterfaces.lean)
adds 26 strict transitive checks using only `propext`, `Classical.choice`, and
`Quot.sound`. Existing application audits remain intact.
