# Intrinsic Isotypic Decomposition

## Frozen Endpoint

Use the actual distinct isotypic components of a semisimple statistics-algebra
module, not all tableau images, as the decomposition index. Prove stability
under every statistics-linear residual action and an explicit equivariant
direct-sum equivalence, with inclusion and inverse inclusion formulas.
There is no finite-dimensionality or finite-multiplicity requirement.

The statistics-linear residual action is an interface for commuting actions,
not an assertion that arbitrary residual matrices preserve tableau images.
The next adapter must derive this interface from commutation. Partition labels
can then use the pinned complex Specht classification. That classification is
available in `TauCeti.RepresentationTheory.Symmetric.Specht.Complex`; the earlier
inspection of the rational API alone did not establish its absence.

No complete p/y/m/j construction is claimed by this endpoint.

## Partition-Label Adapter

Extend the endpoint by the pinned, proved complex Specht classification and
the universe-safe regular-module class API. Prove that distinct isotypic
components inject into partitions, that a simple constituent's label equals
its Specht type, and that tensor-power residual Hom is a product over exactly
the supported partitions. No finite-dimensional flavor assumption is added.
This gives intrinsic isotypic coordinates, not a chosen tableau or monomial
basis within the multiplicity spaces.

## Result And Source Map

Both frozen endpoints are proved:

- [IsotypicResidual](../../../Math/RepresentationTheory/IsotypicResidual.lean):
  canonical sum equivalence, stability and both inclusion formulas.
- [CommutingStatisticsModule](../../../Math/RepresentationTheory/CommutingStatisticsModule.lean):
  derives statistics-algebra linearity from commutation and gives a scalar-level
  carrier equivalence and residual-Hom product.
- [DirectSumResidualHom](../../../Math/RepresentationTheory/DirectSumResidualHom.lean):
  dependent, arbitrary-index Hom restriction and inverse assembly.
- [IsotypicClassMap](../../../Math/RepresentationTheory/IsotypicClassMap.lean)
  and [SpechtIsotypicLabels](../../../Math/RepresentationTheory/SpechtIsotypicLabels.lean):
  universe-safe, injective partition labels and their Specht characterization.
- [TensorStatisticsIsotypic](../../../Math/RepresentationTheory/TensorStatisticsIsotypic.lean):
  tensor-power specialization and supported-partition coefficient equivalence.
- [RelationStatisticsIsotypic](../../../Math/RepresentationTheory/RelationStatisticsIsotypic.lean):
  quotient descent followed by the nonredundant block classification.

For the quotient adapter, stability under statistics is an explicit input in
addition to residual stability. It is not automatically true of arbitrary input
relations. This makes the application condition visible without claiming a
failure of the previously proved relation completeness theorem.

Mathematical inputs are proved mathlib Maschke/isotypic results and pinned
TauCeti complex Specht/class-dictionary theorems. No paper theorem is imported
as an unchecked premise. The
[persistent audit](../../../Math/RepresentationTheory/Audit/AuditStatisticsIsotypic.lean)
checks 23 declarations transitively against standard Lean axioms only.

## Verification

Verified at stage 01: focused audit passed (23 strict transitive checks),
full `lake build` passed (6,364 jobs), layout passed (1,040 modules), local
links passed (381 Markdown files, 2,604 links), and `git diff --check` passed.
Pins and axiom allowances are unchanged; no merge is authorized.
