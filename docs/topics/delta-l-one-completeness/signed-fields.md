# Signed-field support and shared qque input

[DeltaLOneSignedInput](../../../Physics/StandardModel/Operators/DeltaLOneSignedInput.lean)
defines invariant exterior coefficients on the sum of all ten signed fermion
species, independently of any contraction formula. `sector` imposes only a
specified lepton degree. It does not impose baryon degree, hypercharge neutrality,
Weyl parity, or support in four selected families.

[DeltaLOneSignedFields](../../../Physics/StandardModel/Operators/DeltaLOneSignedFields.lean)
instantiates the standard gauge and Weyl actions. The negative species have
contragredient gauge actions and opposite Weyl chirality. Their residual
multiplicities are independent supplied representations, not silently identified
with a dual or conjugate multiplicity. No finite-dimensionality is needed.

On a nonzero pure-species restriction of lepton degree one:

- the full hypercharge circle forces zero hypercharge;
- the SU(3) center forces color triality zero;
- an SL(2,C) diagonal element forces even left-Weyl parity, in every slot order;
- these necessary conditions force exactly duql, qque, qqql or duue.

`four_candidates` and `vanish_outside_four` are the support endpoints.
`baryonDegree_of_nonzero` derives three times baryon degree equal to three;
`no_conjugates_of_nonzero` derives absence of conjugate species. Both are
conclusions, not extra input hypotheses.

[ExteriorWeightSupport](../../../Math/RepresentationTheory/ExteriorWeightSupport.lean)
and [FiniteSpeciesExterior](../../../Math/RepresentationTheory/FiniteSpeciesExterior.lean)
provide reusable eigenvalue constraints, typed pure-species restriction and
extensionality. The Weyl extension uses arbitrary tensor-product bases; it
does not assume finite-dimensional flavor spaces or increase heartbeat limits.

## qque

[QquePhysicalOrderedCompleteness](../../../Physics/StandardModel/Operators/QquePhysicalOrderedCompleteness.lean)
and [QquePhysicalExteriorCompleteness](../../../Physics/StandardModel/Operators/QquePhysicalExteriorCompleteness.lean)
classify the shared physical qque fields under the common gauge, Weyl and residual
group by residual coefficients symmetric in the two quark flavors. Ordered and
exterior inverses and supplied actual-field transport are proved.

[QquePhysicalResidualHom](../../../Physics/StandardModel/Operators/QquePhysicalResidualHom.lean)
compares this space with the existing qque Hom criterion when the up and electron
multiplicities are supplied as linear duals. Only this dual-to-Hom conversion
requires their finite-dimensionality. `legacyEquiv` is a comparison through the
same residual Hom, not a claim that the legacy tensor pullback has been identified
literally. The new exterior equivalence extracts raw ordered restriction, whereas
the old qque convention extracts half that restriction; their probe normalization
must not be conflated.

## Conjugation

[ExteriorConjugation](../../../Math/RepresentationTheory/ExteriorConjugation.lean)
proves conjugation of coefficients as a semilinear equivalence.
[DeltaLOneConjugation](../../../Physics/StandardModel/Operators/DeltaLOneConjugation.lean)
restricts this to lepton degree `d` and `-d`, with nonzero equivalence. Its explicit
model inputs are an equivariant semilinear field involution and species reversal.
It does not assert a canonical involution on arbitrary unrelated residual
multiplicities, nor a complex-linear identification with their duals.

## Full-sector species split

[FiniteSpeciesProjection](../../../Math/RepresentationTheory/FiniteSpeciesProjection.lean)
constructs linear projectors for permutation-stable species support, proves their
pure-species evaluation formula, and proves both inverse identities for finite
disjoint support partitions. Its alternatization normalization is `1/24` for
four slots, separately from each individual family's repeated-species normalization.

[DeltaLOneFourFamilyDecomposition](../../../Physics/StandardModel/Operators/DeltaLOneFourFamilyDecomposition.lean)
applies these projectors to the four count patterns. `sector_eq_partition` proves
that the original lepton-degree-one invariant sector equals the supported
partition space; this is a theorem, not its input definition. `equiv` splits
it into the four intrinsic family sectors, with inverse given by their sum.
`nonzero_iff` proves existence iff some family sector is nonzero.

The fiber-cardinality lemma `FiniteSpeciesExterior.permutation_of_counts`
constructs a slot permutation from equal species counts without listing all
permutations. `orbit` applies it to each of the four families. `family_ext` and
`canonical_ext` prove that the standard ordered restrictions determine each
family and the full sector respectively, with signs supplied by alternating-map
permutation identities. These extensionality lemmas alone do not assert
surjectivity; the following assembly theorem establishes it separately.

## Residual product and inverse

[SpeciesPatternAssembly](../../../Math/RepresentationTheory/SpeciesPatternAssembly.lean)
extends invariant ordered multilinear coefficients to the full field sum by
alternatization divided by the pattern's stabilizer cardinality. It proves
support, canonical restriction, and both inverses without a list of coordinate
elimination cases. The four stabilizer sizes are `1, 2, 6, 2`; these are distinct
from the `24` normalization used for the species projectors.

[DeltaLOneFamilyCompleteness](../../../Physics/StandardModel/Operators/DeltaLOneFamilyCompleteness.lean)
identifies the intrinsic summands with the existing individual ordered
classifications. Compatibility means no restriction for duql, first-two-slot
antisymmetry for qque/duue, and the two adjacent antisymmetries for qqql. The
existing local classifications then remove all gauge and Lorentz conditions.

[DeltaLOneCoefficientCompleteness](../../../Physics/StandardModel/Operators/DeltaLOneCoefficientCompleteness.lean)
composes these four maps with the independent species split to a residual-Hom
product. `extract_reconstruct` and `reconstruct_extract` prove surjectivity and
injectivity in both directions. `negativeEquiv` composes the previously supplied
conjugation interface with this classification; the conjugation hypotheses
remain explicit, not inferred for independent multiplicities.

[DeltaLOneInputTransport](../../../Physics/StandardModel/Operators/DeltaLOneInputTransport.lean)
preserves lepton degree under supplied species-wise equivariant field
identifications and exposes `onFieldsEquiv`. A charge signature alone is not a
field identification. [Regression controls](../../../Physics/StandardModel/Operators/DeltaLOneRegression.lean)
check neutral one-generation dimension four, missing-species vanishing,
nontrivial scalar residual charges, and the repeated-species normalization.
All bounded endpoint obligations are discharged. The user-authorized master
merge is `checkpoint 01`; merged-state builds and audits passed, as recorded in [results](results.md).
