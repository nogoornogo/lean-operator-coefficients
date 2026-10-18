# Results and boundaries

## Independent sector and completeness

[WeinbergSMInterface](../../../Physics/StandardModel/Operators/WeinbergSMInterface.lean)
defines `ModelSector` as the invariant scalar-valued Hom on
`Λ² Lepton ⊗ Sym² Higgs`. It is not defined as the image of contractions.
The acting group is the explicit product
`((SU(3) × SU(2) × Circle) × SL(2,ℂ)) × R`, with the repository's left-Weyl
convention and integral hypercharge normalization `6Y`.
Lepton hypercharge is `-3` and Higgs hypercharge is `3`; their phases cancel
on the mixed domain. No assertion about arbitrary global gauge-group quotients
or additional fields is needed.

`homEquiv` classifies this entire sector by
`Hom_R(Sym² F, trivial ℂ)`. Its inverse constructs a coefficient from any
residual intertwiner; both inverse identities are part of the linear equivalence.
`exists_nonzero_iff` is therefore necessary and sufficient, not just a
construction of one allowed contraction.

`Inputs` contains equivariant identifications of supplied actual lepton and
Higgs representations with these field models. `onFieldsEquiv` and
`exists_on_fields_iff` give the same classification on their independently
defined `Sector`. No spanning or nonzero-coupling hypothesis is hidden in
the input package. Finding these identifications in a UV model remains the
model author's responsibility.

## Proof structure and normalization

- [MixedSquareDescent](../../../Math/RepresentationTheory/MixedSquareDescent.lean)
  identifies mixed alternating/symmetric maps with linear maps on the mixed
  exterior/symmetric domain, including equivariance.
- [ExteriorSquareTensorDescent](../../../Math/RepresentationTheory/ExteriorSquareTensorDescent.lean)
  descends antisymmetric tensor coefficients through the exterior square.
- [WeylPairInvariant](../../../Physics/FieldTheory/Spinor/WeylPairInvariant.lean)
  proves that two-left-spinor invariant coefficients form the epsilon line.
- [WeinbergWeakInvariant](../../../Physics/StandardModel/Gauge/WeinbergWeakInvariant.lean)
  proves the weak invariant line after Higgs symmetrization, using the existing
  symmetric-square/triplet classification.
- [WeinbergResidualHom](../../../Physics/StandardModel/Operators/WeinbergResidualHom.lean)
  extracts both local factors and proves `exchange_iff`: fermion exchange is
  equivalent to symmetry of the residual flavor coefficient.
- [WeinbergModelSector](../../../Physics/StandardModel/Operators/WeinbergModelSector.lean)
  reconnects this regrouped tensor calculation to the independent field-order
  exterior/symmetric sector.

The weak factor is

```text
K(x,y;h₀,h₁) = (ε(x,h₀) ε(y,h₁) + ε(x,h₁) ε(y,h₀)) / 2.
```

Together with the normalized spin epsilon it multiplies the symmetric
residual flavor form. The weak probe `(e₀,e₀;e₁,e₁)` and spin probe `(e₀,e₁)`
both give one. The factor `1/2` disappears for equal Higgs inputs.

## Specified VEV and controls

[WeinbergMajorana](../../../Physics/StandardModel/Operators/WeinbergMajorana.lean)
evaluates at the supplied neutral direction `(0,v)`. The actual exterior
evaluation `WeinbergSMInterface.mass_evaluation` equals the symmetric mass
form `v² κ`, with no unspecified normalization factor.

For `v ≠ 0`, `majoranaEquiv` and `onFieldsMajoranaEquiv` are linear
equivalences to invariant symmetric flavor coefficients. The adapter `mass`
constructs the existing `InvariantWeylMass.SymmetricMass`; `mass_nonzero_iff`
states its form is nonzero exactly when the sector coefficient is nonzero.
For `v = 0`, the mass form is zero. The remaining invariance asserted for
the flavor mass is under `R`, not the broken electroweak group.

[WeinbergScalarFlavor](../../../Physics/StandardModel/Operators/WeinbergScalarFlavor.lean)
proves a nonzero one-dimensional flavor coefficient exists iff its residual
character squares to one. A nontrivial order-two character is explicitly
allowed. Trivial one-generation flavor gives `ModelSector ≃ₗ ℂ` and finrank
one. The residual classification also proves vanishing for zero flavor
(`eq_zero_of_subsingleton`). These statements require no general
finite-dimensionality assumption.

[WeinbergGrading](../../../Physics/StandardModel/Operators/WeinbergGrading.lean)
records `(ΔB,ΔL)=(0,2)`, neutral hypercharge and engineering dimension five.
Scaling both lepton inputs multiplies the coefficient by `z²`; conjugating
the evaluation for `z : Circle` changes this to `(z⁻¹)²`. This is a grading
statement, not imposed lepton-number invariance.

## Exclusions

Completeness is for one specified derivative-free `LLHH` pattern and one
Higgs doublet with trivial residual action. It is not completeness of all
ΔL=2 operators. Multiple Higgs species, higher dimensions/derivatives,
nontrivial Higgs residual action and arbitrary spectrum classification are
outside this topic. So are UV/seesaw matching, vacuum selection, numerical
mass predictions, nondegeneracy, mixing, RGE and rates. A nonzero invariant
space does not force a UV model to generate a nonzero coefficient.
