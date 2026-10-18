# Executable joint-source metadata

The mathematical single-spin, paired-spin, color/single-spin and Q exterior
presentations admit executable syntax functions, with ordinary proofs of
correspondence. These functions construct color/weak/left/right metadata
directly, without projecting it from representation-valued presentation proofs.
They compute expressions, not a general support decision or multiplicity.

[JointSourceData](../../../../../Math/RepresentationTheory/JointSourceData.lean)
provides atoms and single/paired-spin degree functions. `single_eq` and
`doubletPair_eq` prove equality to existing actual presentations, including
zero and overflow. Both independent spin placements are covered.

[ColoredSourceData](../../../../../Math/RepresentationTheory/ColoredSourceData.lean)
preserves the exact ordered sum/tensor expression, including repeated summands,
for colored and Q exterior sources. `colored_eq` and `quark_eq` are uniform
in degree and spin placement; `conjugateColored_eq` and `conjugateQuark_eq`
transport actual dual presentations using the executable syntactic dual.
Theorems are proved by structural cases and rewriting existing expression
correspondences, without closed support computations.

[JointContentData](../../../../../Math/RepresentationTheory/JointContentData.lean)
uses compact numeric occupation indices and executable three-generation/species
tensor composition. `choiceEquiv` reindexes to the original generation choices.
Given uniform core-expression equalities, `occupied_eq` proves equality of
composed expressions for any indexed dictionary in the existing joint group.
No representation decompositions or branching laws are added as assumptions;
the input equalities state exactly the required generic interface.

The strict [audit](../../../../../Math/RepresentationTheory/Audit/AuditJointSourceData.lean)
covers all 56 new named declarations, with only `propext`, `Classical.choice`
and `Quot.sound` permitted transitively. The new proof sources use structural
proofs rather than computational support proofs. They reuse existing proved
mathematical decomposition and compact-occupation results.

The subsequent [SM connection](../Physics/SM_JOINT_SUPPORT_DATA.md) provides
actual full support/Higgs/original-space equivalence and ordinary downstream
consumers. It uses an explicit expression field and the same actual joint
source, avoiding the earlier dependent projection comparison. The earlier
[partial-result stop](../../../../topics/sm-support-evaluator-feasibility/data-layer-results.md)
remains historical evidence, with [revised verification](../../../../topics/sm-support-evaluator-feasibility/data-connection-results.md)
recording completion. No generic compiled search solver is claimed.
