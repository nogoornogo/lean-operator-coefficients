# Single-Higgs Signed-Family Decomposition

## Verified Statement

[BnvSevenFamilyDecomposition](../../../Physics/StandardModel/Operators/BnvSevenFamilyDecomposition.lean)
identifies the independent BNV degree `(4,1)` coefficient space with the product
of eight typed ordered spaces: the four positive patterns and their four
negative-baryon partners. The ordered spaces retain actual gauge, Weyl and
residual invariance and identical-fermion exchange constraints.

`support_of_nonzero` derives the eight species-count supports from the full
input's invariance and BNV grading. `sector_eq_partition` proves equality of
the independent input with that derived support space. `equiv` and
`orderedEquiv` have both inverse identities, not only an injective restriction.
`nonzero_iff` and `forbidden_iff` transfer existence and total vanishing to the
eight ordered factors.

No conjugation map between independent positive/negative flavor carriers is
assumed. All their algebraic residual actions and both scalar actions remain
independent inputs. No finite-dimensionality of multiplicities is required.

## Reusable Construction

[MixedSingleSpeciesProjection](../../../Math/RepresentationTheory/MixedSingleSpeciesProjection.lean)
constructs the linear, idempotent support projector for a permutation-stable
predicate on fermion labels and the boson species. Its pure-value formula is
proved by finite multilinear expansion and normalized alternatization.
Consumers use proved projection equations rather than unfold the species sum.

[MixedSingleSpeciesPartition](../../../Math/RepresentationTheory/MixedSingleSpeciesPartition.lean)
splits a finite disjoint union of such supports, with sum reconstruction and
both inverse identities. `equivOfEq` performs the support-space transport
before field specialization, avoiding unnecessary expansion of the concrete
finite-species projector in consumer proofs.

The construction works for arbitrary fermion slot count and one boson.
This generality does not establish higher-degree SM local completeness.

## Remaining Endpoint Inputs

The ordered factors still contain local gauge/Weyl invariance constraints.
They are not yet the explicit residual-Hom factors of the acceptance gate.
The charged typed regroupings, actual local exchange maps, scalar-free signed
degree endpoint, full seven-dimensional residual product, and the higher-degree
local dictionaries remain outstanding. Neither seven nor eleven is complete.

## Verification

- Focused `AuditBnvBoundedSupport`: 111 strict transitive checks pass.
- Full `lake build`: 6,466 jobs pass.
- Layout: 1,139 modules pass.
- Local documentation links and `git diff --check`: pass.
- Dependency/toolchain pins and root README are unchanged.

No raised heartbeat or recursion limit is used by these new modules.
