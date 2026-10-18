# Graded Completeness Naturality And Restriction

## Result

The [graded completeness equivalences](GRADED_OPERATOR_COMPLETENESS.md) commute
with species-preserving changes of field presentation and restriction of the
residual group. For every mixed degree `(n,m)`, including zero degrees,

`E_source (pull_input f) = pull_Hom (E_target f)`

for field changes, and

`E_restricted (restrict_input f) = restrict_Hom (E_original f)`

for a group homomorphism `j : H' -> H`. Reconstruction obeys the inverse
squares. The statements extend to permutation-stable support selection and
the all-degree product / direct-sum functional presentation.

For `H_small <= H_large`, restriction is injective: allowance for the larger
group implies allowance for the smaller group, and prohibition for the smaller
group implies prohibition for the larger group. Neither converse is asserted.
Surjective `j` gives equivalences, including nonfaithful covers of the supplied
actions. This does not assert that an arbitrary action descends through a cover.

## Inputs And Scope

The local group is fixed. The groups are abstract groups, with no topological
or algebraic-geometric structure required; finite
species sets and complex local/multiplicity modules are supplied. No finite
dimension, compactness, continuity or semisimplicity is required. Field changes
are species-wise invertible equivariant maps compatible with the local action.
Factorwise local/multiplicity equivalences supply this interface via
[LocalMultiplicityEquiv](../../../../../Math/RepresentationTheory/LocalMultiplicityEquiv.lean).
The implementation also accepts paired-field equivalences with that proved
compatibility, without requiring a particular tensor factorization of the map.

Support predicates must be permutation-stable and unchanged by the comparison.
The bounded statements are instances with `GradedMixedCompleteness.boundedAllowed`;
weights and selected charge conditions are retained, not recomputed. No uniform
finite cutoff is inferred from the all-degree result.

The content-wise comparisons use the same `x.out` profile representatives on
both sides. They prove naturality under the stated field-presentation changes
and residual homomorphisms within that fixed classical implementation.
They do not compare two different choices of quotient representatives, relabel
species, or prove a representative-reselection coherence theorem.

## Proof Structure

[RelationQuotientNaturality](../../../../../Math/RepresentationTheory/RelationQuotientNaturality.lean)
constructs maps on stable-relation quotients directly, with generator,
identity and composition formulas.
[LocalCoinvariantNaturality](../../../../../Math/RepresentationTheory/LocalCoinvariantNaturality.lean)
proves preservation of the span of local-action differences.
[LocalRelationNaturality](../../../../../Math/RepresentationTheory/LocalRelationNaturality.lean)
then transports the image of the exchange relations. Equivalences have explicit
two-sided quotient inverses.

[TypedMixedExchangeNaturality](../../../../../Math/RepresentationTheory/TypedMixedExchangeNaturality.lean)
proves preservation of the actual signed fermion and unsigned boson relations.
[TypedMixedCarrierNaturality](../../../../../Math/RepresentationTheory/TypedMixedCarrierNaturality.lean)
separates carriers independently of functional completeness.
[TypedMixedSeparatedTransport](../../../../../Math/RepresentationTheory/TypedMixedSeparatedTransport.lean)
uses those carrier equivalences and direct ordered quotient maps. It does not
define residual transport by conjugating coefficient completeness.

[GradedCompletenessFieldTransport](../../../../../Math/RepresentationTheory/GradedCompletenessFieldTransport.lean)
compares the actual exterior/symmetric field pullback with these independent
content-wise maps, then proves extraction and reconstruction, selected-support
and all-degree squares. Functionals are contravariant. The all-degree Hom map
uses only independent factor maps and the direct-sum universal property.

[GradedCompletenessRestriction](../../../../../Math/RepresentationTheory/GradedCompletenessRestriction.lean)
keeps underlying functionals unchanged and verifies the pulled-back residual
action on each quotient. Its
[all-degree extension](../../../../../Math/RepresentationTheory/GradedCompletenessAllRestriction.lean)
proves injectivity, the allowance/prohibition directions, surjective
equivalences and the direct-sum squares. The existing
[species pullbacks](../../../../../Math/RepresentationTheory/MixedSpeciesTransport.lean)
and ordered pullbacks satisfy identity/composition laws. The general
[square laws](../../../../../Math/LinearAlgebra/CompletenessSquareLaws.lean)
transfer those proved laws to output maps without defining them through `E`.

## Consumers And Verification

[CompletenessNaturalityExamples](../../../../../Math/RepresentationTheory/CompletenessNaturalityExamples.lean)
checks mixed degree `(1,2)`, a surjective cover, a subgroup restriction that is
not surjective, and containment of stabilizers after adding preserved data.
The latter uses only established subgroup containment; it does not classify a
new stabilizer.

The persistent
[strict transitive audit](../../../../../Math/RepresentationTheory/Audit/AuditCompletenessNaturality.lean)
allows only `propext`, `Classical.choice` and `Quot.sound`. The
[topic results](../../../../topics/graded-completeness-naturality/results.md) record
the focused and full-build acceptance evidence.

## Boundaries And Citation Role

This is an internal algebraic integration theorem, not an extension of the
literature verification coverage. It does not compute arbitrary residual Hom,
classify new physical sectors or imply inevitable BNV. Species relabeling,
local-group changes, derivatives, EOM/IBP, amplitudes, rates and external
generators are outside this endpoint. No external mathematical theorem is
added as a premise. See the [assumptions ledger](../../inputs/Math/ASSUMPTIONS.md).
