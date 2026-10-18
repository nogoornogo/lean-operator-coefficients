# Relation-Quotient Completeness

## 1. Result and status

Proved algebraic presentation theorem: a coefficient satisfying specified
linear exchange relations is exactly an equivariant Hom from the corresponding
input quotient. With a proved finite local contraction basis, this gives a
residual-Hom classification with explicit extraction and reconstruction.

## 2. Inputs and conclusion

The general quotient theorem accepts an arbitrary field, residual group,
source/target representations and a stable relation submodule R. It constructs
the equivalence between equivariant maps annihilating R and Hom from U/R.
No finite dimensionality, topology or invariant complement is required.

The finite-local theorem works over C. Its inputs are a local representation A,
arbitrary residual representation X, a finite index I, contractions p_i and
probes v_i with p_i(v_j) = delta_ij, and a proof that every local invariant
functional is their linear combination. Specified equivariant local/flavor
exchanges and scalar signs are additional inputs. Its conclusion is

```text
exchange-constrained invariant coefficients on A tensor X
  ≃ Hom_H((I →₀ X)/R, C).
```

Completeness of the local basis is a premise, not a discovery algorithm.

## 3. Definitions and conventions

For the existing pullback exchange convention, let M_j(i,m) be the local
exchange matrix. Generate R by

```text
sum_m single m (M_j(i,m) • exchange_j(w))
  - single i (sign_j • w).
```

This is an input relation, independently specified before its annihilator.
In particular matrix rows act on coefficient coordinates; the dual input
relation uses the corresponding sum of input injections. Residual equivariance
of flavor exchanges proves stability of R.

## 4. Proof structure

`RelationQuotient` proves quotient descent, pullback and both inverse laws.
`ResidualRelationPresentation` identifies coordinate families with maps on the
finitely supported sum, then identifies the row constraints with annihilation
of R. `FiniteLocalRelationCompleteness` composes this equivalence with the
existing finite local invariant/statistical classification.

Extraction evaluates the descended map at the quotient of `single i w`.
Reconstruction on pure tensors is the sum of p_i(u) times these evaluations.
`SignedRelationQuotient` also supplies the one-carrier exchange formulation,
including empty relations, identity relations and inconsistent identity signs.

For an equivariant involution t over C, `InvolutionYoung` proves that the signed
relation quotient is equivariantly equivalent to ker(t - s id), for s^2 = 1.
Its forward map is the projector (id + s t)/2 and its inverse is quotient
inclusion. The +1 and -1 components form the whole representation as a product.
The tensor-exchange specialization gives the two S2 Young shapes, with no
dimension premise.

`TwoSlotYoungSquares` identifies these components with the independently
defined symmetric and exterior squares by their universal properties. Forward
maps are normalized signed projections of product/wedge generators; inverses
restrict the standard product/wedge projections. Thus tensor square splits
equivariantly as Sym² F × exterior² F. Signed relation quotients have actual
carrier equivalences to these standard squares.

## 5. Lean entry points

For any finite statistics group S whose order is invertible in the scalar
field, `FiniteStatisticsQuotient` uses mathlib's average projection to identify
the span quotient of b(g)u-u with the invariant subrepresentation. An arbitrary
residual action must commute with b. The inverse is quotient inclusion;
normalization is 1/|S|. Twisting by the inverse of a units-valued character
gives the character component, with its eigencondition proved explicitly.
This does not require finite-dimensionality. In characteristic dividing |S|
the stated invertibility premise fails; no such decomposition is claimed.

- [RelationQuotient](../../../../../Math/RepresentationTheory/RelationQuotient.lean):
  `equiv`, `vanish_relations_iff`, `relations_stable`.
- [FiniteStatisticsQuotient](../../../../../Math/RepresentationTheory/FiniteStatisticsQuotient.lean):
  `equiv`, `average_sub_mem`, `characterEquiv`, `mem_twisted`.
- [ResidualRelationPresentation](../../../../../Math/RepresentationTheory/ResidualRelationPresentation.lean):
  `familyEquiv`, `stable`, `admissible`, `equiv`.
- [FiniteLocalRelationCompleteness](../../../../../Math/RepresentationTheory/FiniteLocalRelationCompleteness.lean):
  `equiv`, `extraction`, `reconstruction`, `nonzero_iff`.
- [SignedRelationQuotient](../../../../../Math/RepresentationTheory/SignedRelationQuotient.lean):
  `equiv`, `empty_relations`, `identity_relations`, `identity_relations_top`.
- [InvolutionYoung](../../../../../Math/RepresentationTheory/InvolutionYoung.lean):
  `quotientEquiv`, `splitting`, `coefficientEquiv`.
- [TwoSlotYoung](../../../../../Math/RepresentationTheory/TwoSlotYoung.lean):
  tensor-slot `splitting`, signed quotient equivalences and projector formulas.
- [TwoSlotYoungSquares](../../../../../Math/RepresentationTheory/TwoSlotYoungSquares.lean):
  `symmetricEquiv`, `exteriorEquiv`, `splitting`, signed quotient adapters.
- [Weinberg consumer](../../../../../Physics/StandardModel/Operators/WeinbergRelationCompleteness.lean):
  `modelEquiv`, `symmetricHomEquiv`, `modelEquiv_agrees`.

## 6. Scope and limitations

[TensorPermutationStatistics](../../../../../Math/RepresentationTheory/TensorPermutationStatistics.lean)
instantiates finite statistics for every tensor degree and arbitrary complex
flavor. Its pure-tensor convention uses inverse permutation, matching TauCeti.
[YoungTensorProjector](../../../../../Math/RepresentationTheory/YoungTensorProjector.lean)
constructs a residual-equivariant projector for each supplied Young tableau,
by transporting TauCeti's proved rational normalized symmetrizer. The kernel
quotient is equivariantly equivalent to the image, and kernel and image are
complementary. These statements require no finite-dimensional flavor. They do
not assert that distinct tableau images are disjoint or constitute a full
partition-labelled decomposition.

This is a presentation theorem with a two-slot Young decomposition, not a
general EFT enumeration or general p/y/m/j-basis implementation. The intrinsic
partition-labelled extension below is distinct from Schur-Weyl duality; no
general Schur-Weyl theorem is established here.
Specified generators do not automatically prove
generation of a desired permutation group. The new physical quotient adapter
is proved for Weinberg; the other sector endpoints retain their existing
statistical interfaces. The Weinberg comparison remains its explicit Hom-space
equivalence. Separately, the two-slot signed relation quotients are now
identified with the standard square carriers by proved equivariant maps.
No derivatives, EOM/IBP, amplitudes, UV matching or rates are included.

The intrinsic extension in
[CommutingStatisticsModule](../../../../../Math/RepresentationTheory/CommutingStatisticsModule.lean)
proves the nonredundant decomposition for any commuting finite statistics action,
provided the group's cardinal is nonzero in the field. Maschke establishes
semisimplicity, including for infinite-dimensional carriers. Residual maps
preserve actual isotypic components, and their sum is an equivariant equivalence.
[DirectSumResidualHom](../../../../../Math/RepresentationTheory/DirectSumResidualHom.lean)
then gives a product of block Homs with inverse assembly.

[SpechtIsotypicLabels](../../../../../Math/RepresentationTheory/SpechtIsotypicLabels.lean)
connects TauCeti's complex Specht classification to arbitrary-dimensional modules
through regular-module classes. A simple constituent's label is its Specht type;
labels are injective and the set of occurring components is finite.
[TensorStatisticsIsotypic](../../../../../Math/RepresentationTheory/TensorStatisticsIsotypic.lean)
gives supported-partition residual Hom coordinates in every tensor degree.
This is a full intrinsic isotypic splitting, not a tableau basis or a
multiplicity-space basis. Individual tableau images are not claimed to form
the nonredundant direct sum.

[RelationStatisticsIsotypic](../../../../../Math/RepresentationTheory/RelationStatisticsIsotypic.lean)
composes input-relation descent with the same decomposition. The relation space
must be stable under both actions. This condition is explicit: arbitrary
residual-stable relations need not admit the original statistics action.

[FiniteLocalStatistics](../../../../../Math/RepresentationTheory/FiniteLocalStatistics.lean)
derives genuine input statistics from the proved finite local dictionary and
commuting local/flavor actions. Its computed matrices obey the group law and
agree with the coefficient-side exchange matrices.
[FiniteLocalIsotypicCompleteness](../../../../../Math/RepresentationTheory/FiniteLocalIsotypicCompleteness.lean)
connects the actual local coefficient sector to the input relation quotient
and its product of residual-Hom isotypic blocks. Probe extraction and contraction
reconstruction are explicit. For units-valued character relations,
[CharacterRelationStability](../../../../../Math/RepresentationTheory/CharacterRelationStability.lean)
proves statistics stability; it is not a new application assumption. Forward
coefficient pullback remains contravariant, while the input action is a genuine
representation. No finite-dimensional flavor hypothesis is added.

[MultiplicityCoordinates](../../../../../Math/RepresentationTheory/MultiplicityCoordinates.lean)
proves existence of simple-copy coordinates for each intrinsic isotypic block,
with an arbitrary multiplicity index. These coordinates are noncanonical;
their residual action is transported in full and may mix copies. Changes
between chosen coordinates are equivariant, and residual coefficients admit
an inverse Hom transport with explicit evaluation formulas.
[FiniteLocalBasisConversion](../../../../../Math/RepresentationTheory/FiniteLocalBasisConversion.lean)
converts two proved normalized/exhaustive local dictionaries by their cross-probe
matrix, with its inverse and equality of reconstructed coefficients. This does
not yet identify coordinates with a canonical statistics-Hom multiplicity space
or with Li's basis conventions.

[StatisticsMultiplicityCoordinates](../../../../../Math/RepresentationTheory/StatisticsMultiplicityCoordinates.lean)
constructs those chosen presentations for the actual commuting-statistics blocks,
refines the full block-Hom product and proves extraction, inverse reconstruction,
zero detection and independence under change of presentation.
`FiniteLocalIsotypicCompleteness.characterMultiplicityEquiv` applies this to the
independently defined local/flavor character sector. Coordinate existence is
proved internally. The concrete
[two-contraction controls](../../../../../Math/RepresentationTheory/FiniteLocalBasisConversionControls.lean)
verify sum/difference dictionaries and both conversion matrices for arbitrary
residual flavor. This completes the chosen-coordinate stage, not a canonical
statistics-Hom realization or Li p/y/m/j identification.

## 7. Sources and verification

Li et al. is motivation for the subsequent basis program, not an external
theorem premise here; see the related
[literature comparison](../../../../topics/operator-completeness-interface/README.md#relationship-to-li-et-al).
All descent and classification claims above are Lean proofs.

Persistent audits:
[24 mathematical checks](../../../../../Math/RepresentationTheory/Audit/AuditRelationCompleteness.lean)
and [9 Weinberg checks](../../../../../Physics/StandardModel/Operators/Audit/AuditWeinbergRelationCompleteness.lean).
They allow only `propext`, `Classical.choice` and `Quot.sound` transitively.
[Signed controls](../../../../../Math/RepresentationTheory/SignedRelationControls.lean)
verify both statistics signs, nonzero descended examples and the inconsistent
identity zero quotient. Build commands and integration status belong to the
[topic record](../../../../topics/derivative-free-completeness/README.md).
The [two-slot audit](../../../../../Math/RepresentationTheory/Audit/AuditTwoSlotYoung.lean)
performs 36 strict transitive checks of projectors, equivariant inverse laws,
decomposition, tensor specialization and independent square carrier adapters.
The [finite statistics audit](../../../../../Math/RepresentationTheory/Audit/AuditFiniteStatisticsQuotient.lean)
adds 13 strict transitive checks. The average projection's invariant/image
properties are proved mathlib inputs, not external literature premises.
The [arbitrary-slot Young audit](../../../../../Math/RepresentationTheory/Audit/AuditYoungTensorProjector.lean)
adds 14 strict transitive checks, including the upstream normalization premise.
See the [reuse record](../../../../topics/derivative-free-completeness/arbitrary-slot-young.md)
for the inspected but unconnected Schur-Weyl boundary.
The [isotypic audit](../../../../../Math/RepresentationTheory/Audit/AuditStatisticsIsotypic.lean)
adds 23 strict checks, including the complex Specht classification dependency
and arbitrary-dimensional supported-partition coordinates.
The [finite local statistics audit](../../../../../Math/RepresentationTheory/Audit/AuditFiniteLocalStatistics.lean)
adds 16 strict checks of matrix laws, compatibility, character-relation stability,
quotient extraction/reconstruction and the final block-Hom equivalence.
The [multiplicity-coordinate audit](../../../../../Math/RepresentationTheory/Audit/AuditMultiplicityCoordinates.lean)
performs 31 strict checks of simple-copy existence, coordinate and Hom transport,
the actual block/character-sector consumers, change of choice and concrete
finite local dictionary conversion in both directions.
