# Flavored tensor coordinates and constrained residual Hom

The typed tensor-coordinate and exchange components identify the actual
`DeltaBTwoModelInterface.ModelSector` with a constrained residual Hom, without
a Young-diagram decomposition premise. The physical inverse is an explicit
normalized alternating lift, not a surjectivity assumption.

## Exact statements

Let `V i` be arbitrary complex flavor spaces in the six ordered slots and let
`Q = Color tensor RightWeyl`. A coefficient is an independently supplied
multilinear map on `Q tensor V i`, invariant under independent color and Weyl
actions. Fixing the six flavor vectors gives an ordinary six-quark coefficient.

- Its 25 color/Weyl coordinates are bundled multilinear flavor tensors, not
  arbitrary functions and not constant scalar coefficients.
- They determine the coefficient on full tensor-product slots. Decomposable
  inputs determine those slots by tensor-product basis extensionality.
- For finite-dimensional flavor spaces, `assemble` extends every multilinear
  25-coordinate tensor to a color/Weyl invariant coefficient. Both extraction
  and reconstruction identities are proved.
- With residual representations `r i`, residual invariance of the coefficient
  is equivalent to invariance of the coordinate tensor. The latter is exactly
  `Hom_H(tensor_i V i, trivial_H(C^(5 by 5)))`, by the heterogeneous tensor-product
  universal property. `assembleHom_residualHom` and `residualHom_assembleHom`
  give both inverse identities, without an assumed spanning assertion.

The coordinate tensor carries the entire ordered contraction information.
Fermi statistics still imposes conditions on this Hom; it is not an arbitrary
25-tuple of independent residual invariants.

## Exchange equations

For a common flavor carrier `F` in all slots, set `c(t)` to the 25-coordinate
array and let `sigma_g` be the four within-species transpositions. The exact law is

`transform_g(c(t composed sigma_g)) = -c(t)`.

`transform_g` uses the already proved color and Weyl permutation matrices.
The flavor arguments are permuted simultaneously. `statistics_iff` proves
necessity and sufficiency of these equations on the full flavored tensors.
`swaps_iff_species` proves that the four equations imply the sign rule for
every species-preserving permutation, reusing the certified 48-word cover.

`statisticsLinearEquiv` is a linear equivalence between independently specified
color/Weyl/residual invariant, species-alternating coefficients and the residual
Hom satisfying those four explicit equations. `exists_nonzero_statistics_iff`
preserves nonzero-coefficient existence. It is not an unconstrained Hom out of
a permutation quotient.

## Heterogeneous and scalar specializations

`SixQuarkTypedFlavor` uses a dependent `(U,D,U,D,D,D)` family, with proved
same-species fiber equivalences for the four generators. Neither `U = D` nor
an equivariant equivalence between them is assumed. `homLinearEquiv` classifies
the independently specified gauge/Weyl/residual invariant tensors satisfying
the typed exchange equations; `exists_nonzero_iff` gives its nonzero criterion.
`typed_swap_full` extends the decomposable-input equations to full tensor inputs.

For common scalar flavors with trivial residual action, `scalarFlavorEquiv`
forgets/adds the scalar tensor factors with both inverses. `twoProbeEquiv` and
`homTwoProbeEquiv` recover the established two-probe inverse, and the two
corresponding finranks are proved equal to two.

`DeltaBTwoFlavorBridge.reorder` transports the model's nested tensor order to
`(Color tensor Spin) tensor Flavor`. Its up/down action theorems explicitly
retain hypercharge phases and the residual action. `physical_invariance_iff`
proves necessity and sufficiency of independent color/Weyl/residual invariance,
using the explicitly proved degree `(2,4)` phase product.

`restrictSector` takes an independently specified actual exterior coefficient
to the reordered heterogeneous tensor slots. Its invariance and typed exchange
laws are proved, and `sectorHom` extracts constrained residual Hom coordinates.
`restriction_slots_eq` proves, at the alternating-map level, that equality of
the restrictions forces equality on the standard species slots.
`restrictSector_injective` transfers this fact to `ModelSector` using generic
`SixSlotSpeciesRestriction.sector_ext`. The extraction `sectorHomLinear` is
linear and injective, with `sectorHom_ne_zero_iff` for each physical coefficient.
`onFieldsHomLinear`, `onFieldsHom_injective` and `onFieldsHom_ne_zero_iff`
transport these results to actual fields through the supplied `Inputs`.
`liftSector` gives the physical inverse by species projection followed by
alternatization divided by 48 and descent through the exterior universal
property. `descended_degree` proves degree `(2,4)`, and invariant descent uses
the proved physical action identities. `restrict_lift` and
`lift_restrictedCoefficient` prove both inverse identities. `sectorHomEquiv`
and `onFieldsHomEquiv` therefore classify the full physical and supplied
actual-field sectors, respectively. `exists_nonzero_sector_iff` is now a
nonzero-existence iff onto the entire constrained Hom.
The elaboration issue in the injectivity transfer was resolved by local
opacity of representation definitions, without increasing resource limits.

## Physical one-generation endpoint

`DeltaBTwoFlavorOneGeneration.typedScalarEquiv` removes/adds the scalar flavor
factors with both inverse identities. It uses `H = Unit` and trivial scalar
up/down residual representations. Composing it with `sectorCoefficientEquiv`
and the established `coefficientProbeEquiv` gives `physicalTwoProbeEquiv` on
the independent physical exterior sector. Its inverse is explicitly
`liftSector scalar scalar (add (fromProbesCoefficient t))`.

`finrank_physical` and `finrank_hom` prove dimension two for that specialization.
`onFieldsTwoProbeEquiv` and `finrank_onFields` transport it to actual fields
under the supplied equivariant identifications. This is not a dimension-two
claim for arbitrary multiplicities or for arbitrary nontrivial residual
characters on one-dimensional carriers.

The strict transitive audit passes 72 checks. Full repository verification and
integration status are recorded in the topic overview and
[integration record](integration.md). No proof obligation remains in this bounded
classification endpoint. Further all-chirality generalization is deferred.

## Sources

- [Flavor coordinates and exchange equations](../../../Physics/StandardModel/Operators/SixQuarkFlavorCoordinates.lean)
- [Residual Hom and constrained classification](../../../Physics/StandardModel/Operators/SixQuarkFlavorResidualHom.lean)
- [Generic multilinear invariant Hom](../../../Math/RepresentationTheory/MultilinearInvariantHom.lean)
- [Typed up/down flavor Hom](../../../Physics/StandardModel/Operators/SixQuarkTypedFlavor.lean)
- [Scalar-flavor two-probe specialization](../../../Physics/StandardModel/Operators/SixQuarkFlavorOneGeneration.lean)
- [Physical tensor-order/action bridge](../../../Physics/StandardModel/Operators/DeltaBTwoFlavorBridge.lean)
- [Physical scalar-flavor two-probe classification](../../../Physics/StandardModel/Operators/DeltaBTwoFlavorOneGeneration.lean)
- [Topic plan](README.md)
