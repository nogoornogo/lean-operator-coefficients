# Arbitrary Mixed Species Checkpoint

`MixedSpeciesProjection.project_pure` constructs support restriction on actual
exterior/symmetric pure tensors, for arbitrary natural fermion and boson degrees.
Support must be stable under the separate slot permutations. No basis or
finite-dimensional field carrier is needed; only the species alphabets are finite.
The projection is residual-equivariant and fixes supported coefficients.

`MixedSpeciesPartition.equiv` proves both split/join inverses for any finite,
pairwise disjoint family of such supports. Boson slots are not restricted to zero
or one. `TypedPatternSymmetrization.symmetric_pure` reconstructs typed boson
multilinear maps satisfying identical-species exchanges, using the proved
nonzero stabilizer cardinal for normalization. Its vanishing theorem excludes
profiles outside the pattern orbit, including the zero-degree case.

The focused audit passes 13 strict transitive checks (3,183 jobs). Full-build,
layout and link results are recorded in the topic overview after verification.
These results do not yet connect mixed typed contents to local/flavor tensor
regrouping, charge grading or the final SM consumers.

- [Projection](../../../Math/RepresentationTheory/MixedSpeciesProjection.lean)
- [Partition inverses](../../../Math/RepresentationTheory/MixedSpeciesPartition.lean)
- [Typed boson construction](../../../Math/RepresentationTheory/TypedPatternSymmetrization.lean)
- [Audit](../../../Math/RepresentationTheory/Audit/AuditMixedSpeciesPartition.lean)
