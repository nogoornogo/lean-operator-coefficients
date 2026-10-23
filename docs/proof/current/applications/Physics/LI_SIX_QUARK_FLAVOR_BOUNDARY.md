# Printed Six-Quark Basis: Exact Flavor Boundary

## Statement And Scope

In the specified derivative-free right-handed `u²d⁴` sector and the
[recovered epsilon conventions](LI_SIX_QUARK_BASIS.md), the span of all
exchange-word orbits of Li's ten printed seeds is exactly the separating
probe's kernel. It has complex dimension 24, with reconstruction using
the first 24 selected orbit contractions.

For arbitrary residual group `H` and distinct complex multiplicity spaces
`U,D`, the missing probe of an admissible residual Hom is symmetric in two up
inputs and alternating in four down inputs. Its functional descends to
`Sym² U ⊗ Λ⁴ D`. Evaluation recovers the original probe, and vanishing of the
descended functional is equivalent to vanishing of that probe. This is a
universal-quotient factorization, not an eleven-factor Schur decomposition or
a stand-alone classification of all residual intertwiners on that quotient.

If `D` is finite-dimensional and `finrank ℂ D ≤ 3`, the probe vanishes.
The [basis-free physical bridge](GRADED_SIX_QUARK_COMPARISON.md) leaves U arbitrary;
`ModelSector` is linearly equivalent to the residual Hom
whose values lie in the printed orbit span. Both inverse identities are
explicit. All four typed statistics equations and residual equivariance
remain imposed; these are not 24 unconstrained flavor maps.

## Proof Structure And Interfaces

- [Printed span](../../../../../Physics/StandardModel/Operators/BaryonTwo/Li/LiSixQuarkPrintedSpan.lean):
  `printedSpan_eq_kernel`, `printed_finrank`, `printed_reconstruction`.
- [Flavor projection](../../../../../Physics/StandardModel/Operators/BaryonTwo/Li/LiSixQuarkFlavorProjection.lean):
  `missing_exchange`, `missing_zero_iff_printed`.
- [Universal quotients](../../../../../Physics/StandardModel/Operators/BaryonTwo/Li/LiSixQuarkFlavorAlternating.lean):
  `downAlternating`, `up_symmetric`, `missingTensor_apply`,
  `missingTensor_zero_iff`, `missing_zero_of_down_finrank`.
- [Physical completeness](../../../../../Physics/StandardModel/Operators/BaryonTwo/Li/LiSixQuarkPrintedCompleteness.lean):
  `PrintedHom`, `printedHom_iff`, `physicalEquiv` and its two inverse identities.
- [Audit](../../../../../Physics/StandardModel/Operators/BaryonTwo/Li/Audit/AuditLiSixQuarkFlavorBoundary.lean).

The local inverse certificate proves the hyperplane equality. The probe's
character follows from the independent exchange matrices. Adjacent down swaps
generate all permutations, giving an alternating map. Four vectors in down
dimension at most three are dependent, so its value vanishes. Symmetric-power
and exterior-power universal properties give the quotient factorization.

## Citation Role And Boundaries

[Li et al., arXiv:2007.07899](https://arxiv.org/abs/2007.07899), equation (5.63),
supplies candidate expressions, not a trusted completeness premise. The
interpretation and primitive normalizations are those of the parent certificate.
[Generic EFT, arXiv:2201.04639](https://arxiv.org/abs/2201.04639) motivates the
method but does not supply this list.

The printed epsilon-orbit list is therefore complete for down dimension at
most three in this selected sector. The parent four-down-flavor witness
exhibits failure beyond that bound; this does not say that every residual
symmetry permits a missing component. Whole-paper counting polynomials,
other species/chiralities, C-matrix normalization, derivatives, EOM/IBP and
physical matching are outside the result.

## Verification

See the [owning topic](../../../../topics/li-six-quark-flavor-boundary/README.md).
