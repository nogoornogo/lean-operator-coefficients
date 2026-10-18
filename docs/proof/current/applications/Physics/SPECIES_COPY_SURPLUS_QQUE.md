# Species-Dependent Copy Surplus To Physical Qque

## Actual-Mass Statement

[PhysicalSpeciesCopySurplus](../../../../../Physics/FieldTheory/Mass/PhysicalSpeciesCopySurplus.lean)
reuses the existing Species construction separately for Q,uc,ec. Each has its
own finite source A_i, target C_i, copy representations and mass map M_i. The
actual field F, action rho of the SM covering group × H, and original invariant
symmetric mass B remain fixed. F need not be finite-dimensional.

A Realization supplies full-sector injective equivariant embeddings and actual
dual-field maps with the commuting mass squares. It supplies neither light
membership nor a nonzero coefficient. Given a common finite irreducible r,
semisimple A_i and a positive Hom surplus in each species,
`Realization.light_exterior` proves actual kernel ranges lie in B's radical
and carry a nonzero physical qque exterior coefficient. The species embeddings
and surviving coordinate directions may differ.

The right-handed physical up/electron carriers are duals of the actual uc/ec
ranges. Their ambient action, SM and Lorentz invariance, and fermionic exterior
statistics use the existing named interfaces. H acts trivially on spinors.
`Model.arbitrary_mass_light_exterior` applies the result to every invariant
symmetric B when a fixed model derives a Realization for every B.

## Derived All-Mass Constructor

[SpeciesSectorPresentation](../../../../../Physics/FieldTheory/Mass/SpeciesSectorPresentation.lean)
provides a mass-independent sector presentation, separately for each species:

```
rho ≃ external gauge_i a_i × ((external gauge_i c_i)* × rest_i).
```

It requires NoPairings from the source sector to itself and to rest_i, plus
factorization of allowed gauge pairings. `ofIrreducible` derives factorization
from finite gauge irreducibility by the shared Schur theorem; it does not ask
for a mass-dependent factorization certificate. For the fixed Q/uc/ec gauge
representations, [StandardSMIrreducibility](../../../../../Physics/StandardModel/Gauge/StandardSMIrreducibility.lean)
already proves the needed irreducibility facts. A field decomposition and the
NoPairings conditions still must be justified for a chosen dictionary.

For any original B, `massMap` extracts its allowed source/opposite column.
`mass_column` proves it has no other components. `copyMap` and `mass_factor`
derive the residual mass intertwiner; `species` derives the full commuting
square and source injectivity. `modelOfPresentations` combines the three
presentations into the all-B Model. No kernel placement, Dirac ansatz or
qque coefficient is supplied as a premise.

The complementary sector is arbitrary and can carry independent Majorana
masses. No global Dirac normal form, target semisimplicity or finite actual
F/rest is required. The selected finite target supplies the bidual identification.
The theorem is conditional on actual presentation/pairing data, not a proof
that every matter carrier has such a presentation.

## Interpretation And Limits

For trivial H the independent copy counts 3→2, 3→2, 1→0 have positive Hom
surplus for the trivial one-copy r, even though no single common full source
and target were specified. This is a generic supplied-sector consequence,
not a proved UV 40/50 or PS branching/parameter adapter.

The conclusion concerns the participating light ranges, not extension to all
of the radical or an iff classification of allowed qque. Failure of the
shared-r surplus is not a prohibition theorem. The existing common-S/T API
and consumers remain unchanged. Global quotient descent, UV branching/VEVs,
post-EW mixing and all-loop stability remain model obligations.
A nonzero allowed coefficient does not establish generation, matching or decay.

See the [math dossier](../../inputs/Math/SPECIES_COPY_SURPLUS.md),
[strict audit](../../../../../Physics/FieldTheory/Mass/Audit/AuditPhysicalSpeciesCopySurplus.lean),
[exact controls](../../../../../tools/species-copy-surplus/README.md),
and [verification](../../../../topics/species-copy-surplus/verification.md).

The [balanced physical control](../../../../topics/prohibition-converse-boundaries/surplus-results.md)
now proves failure of the converse: equal copy actions with invariant zero mass
have no joint surplus but admit a nonzero participating light exterior qque
coefficient. All mass/embedding/kernel premises are constructed. This preserves
the original sufficient theorem and its distinction from coefficient equivalence.
