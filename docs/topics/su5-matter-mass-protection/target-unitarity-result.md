# Target Unitarity Is No Longer A Supplied Hypothesis

## Statement

`NonScalarInvariantMass.arbitrary_mass_light_exterior_of_continuous` starts with
the same original common-copy carrier, actions and arbitrary invariant symmetric
mass B as the [unified result](unification-result.md). It retains compact
topological H, joint continuity of s/t, finite-dimensional inner-product carrier
interfaces and dim T < dim S. It does **not** require
`IsUnitaryRepresentation t` for the given target inner product.

The conclusion derives three residual-equivariant species maps, exact equality
with B's mass form, membership of actual participating ranges in B's radical,
and nonzero SM/H/Lorentz/fermionic physical qque exterior coefficient on those
original ranges. The mass, fields, residual actions, right-handed dual convention
and positive dimension condition are unchanged. Earlier versions with explicit
target unitarity remain available unchanged.

## Why This Removal Works

[CommonCopyKernel](../../../Physics/FieldTheory/Mass/CommonCopyKernel.lean)
constructs `unitaryTarget` using the existing
[finite-basis compact unitary model](../../../Math/RepresentationTheory/Unitary/FiniteBasisUnitaryModel.lean).
Joint continuity gives continuous matrix coordinates in a chosen finite basis.
Compact unitarization supplies a genuine equivalent unitary action on a Hilbert
copy. This is derived within the repository interfaces, not a new unitary-model
or invariant-metric certificate supplied by the user.

`targetEquiv` is an actual representation equivalence from the original target.
`transportMass` composes each original mass intertwiner with this equivalence.
Since that equivalence is injective, its composition does not change which
source vectors are killed. `kernelEquiv` explicitly identifies the original and
transported kernel representations; both directions retain the same source
vector, and their actions intertwine. Dimension equality is also derived from
the actual linear equivalence.

The existing positive-index/common-constituent theorem is applied only in these
internal proof coordinates. Its three splits are transported back to the
original kernels by `exists_common_split_of_continuous`. The physical exterior
construction therefore uses the original kernels and actual participating ranges,
not a surrogate mass model. The model endpoints are
`NonScalarCopyMass.exists_light_exterior_of_continuous` and the arbitrary-B
endpoint stated above. Original B-radical membership follows from the exact
species mass-form equality, as in the preceding unified theorem.

## What Remains Fixed

This removes invariance of the **given** target metric as an input. It does not
assert that every given target metric is invariant: an equivalent unitary
realization is derived and used internally. Compactness and continuity remain
essential premises of this implementation. The subsequent [algebraic theorem](algebraic-copy-result.md) replaces them by
source semisimplicity, without target semisimplicity. This compact endpoint
retains its original signature. The carrier still has
finite-dimensional inner-product interfaces, common factorized copy actions and
an untouched bar-five with scalar character psi. Additional irreps, independent
species actions, full-light transport and UV/global-group bridges remain outside
this endpoint. Allowed coefficient existence is not UV generation or a rate.

## Verification

The [frozen plan](target-unitarity-plan.md) fixes this phase. Existing strict
transitive audits are extended for all new definitions/theorems; SU(5) audits
continue rejecting original SU(6) module origins. Final commands and results are
in [verification](verification.md). Pins, proof limits and axiom allowances are
unchanged.
