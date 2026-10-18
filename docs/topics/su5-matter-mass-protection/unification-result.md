# Unified Arbitrary Invariant Mass And Non-Scalar Copy Theorem

[NonScalarInvariantMass](../../../GUT/SU5/SelectionRules/NonScalarInvariantMass.lean)
joins the two preceding stages on the actual carrier
`(Ten tensor S) + bar-five + (Ten tensor T)*`. The residual group H is a
compact topological group, with jointly continuous common source/target
representations s/t and a unitary target t. S/T have the stated finite-dimensional
complex inner-product interfaces; H need not be Abelian. The bar-five has an
independent scalar character psi. Gauge and residual actions are genuine
external products. The SM cover is unbroken.

The input B is an arbitrary invariant symmetric complex-bilinear mass. Neither
a Dirac ansatz nor three species-equivariant maps are supplied. For dim T <
dim S, `arbitrary_mass_light_exterior` derives three equivariant maps Mq/Mu/Me,
exact equality of B's form with their species mass, actual participating-range
membership in B's radical, and a nonzero SM/H/Lorentz/fermionic physical qque
exterior coefficient. Right-handed up/electron are the duals of the actual
left-handed ranges, as in the preceding non-scalar model.

The subsequent [target-unitarity removal](target-unitarity-result.md) proves
`arbitrary_mass_light_exterior_of_continuous` without supplied target unitarity.
The original theorem above keeps its original signature; compactness and joint
continuity remain in the new endpoint.

The subsequent [algebraic common-copy theorem](algebraic-copy-result.md) adds
`arbitrary_mass_light_exterior_of_semisimple` for arbitrary H with semisimple
source, removing topology, compactness, continuity and supplied metric invariance.
The target need not be semisimple; the common-copy and dimension conditions remain.

The [pure-carrier continuation](algebraic-carrier-result.md) additionally removes
all norm/inner-product inputs from the named source-semisimple endpoint. It now
uses finite-dimensional complex representations only, on the current carrier.

## Derived Bridges

Finite-dimensional source/target bases provide tensor-to-finite-copy linear
and SM-equivariant equivalences. These are proof coordinates, not a new
restriction on the residual action. Same-side mass pairings vanish by transport
of the already-proved actual SM charge separation. Thus `normal_form` derives
the Dirac cross map from arbitrary B, including the initially admitted
Majorana-type candidates, which vanish for this carrier under unbroken SM.

`coordinateMap` restricts an arbitrary joint intertwiner to SM and changes
coordinates. The existing actual ten Schur classification extracts its three
species matrices. `speciesLinear` turns those coordinates back into maps S → T;
`reconstructedLinear_eq` proves reconstruction of the entire map, including
vanishing of the bar-five-to-target block.

The pure quark/up/electron identities express the original map as the identity
on each actual gauge species tensored with its extracted copy map. Applying
joint equivariance at `(1,h)` and cancelling a nonzero gauge tensor proves
`species_equivariant`. Consequently `quarkMap`, `upMap` and `electronMap` are
actual residual intertwiners derived from B, not assumed certificates.
`species_normal_form` gives the exact mass-form equality.

The previous common-copy kernel theorem then supplies the common surviving
constituent and physical exterior coefficient. Equality of bilinear forms
identifies their radicals, so the actual participating ranges lie in the
radical of the same arbitrary input B. This closes the formerly recorded
unification bridge without additional classification premises.

## Remaining Scope

This is a sufficient nonvanishing theorem for the current common-copy carrier
with positive dimension difference. It is not a necessary-and-sufficient
classification of all mass/representation choices. If dim T ≥ dim S, it makes
no universal nonzero claim. Independently varying residual species actions,
additional matter irreps, compensated UV actions and electroweak breaking are
outside the statement. Arbitrary copy contents are not asserted to satisfy UV
anomaly cancellation or an exact complete SM spectrum.

Whole-light coefficient transport, global-group descent, actual UV residual
mechanisms and all-BNV protection remain in the
[connection ledger](remaining-general-connections.md). An allowed nonzero
coefficient space is not a generated Wilson coefficient or a proton lifetime.

## Verification

The [frozen plan](unification-plan.md) fixes this endpoint. The persistent audit
checks strict transitive axioms and rejects original SU(6) imports. Final
commands/results belong to [verification](verification.md). Existing earlier
statements keep their recorded hypotheses and are reused unchanged.
