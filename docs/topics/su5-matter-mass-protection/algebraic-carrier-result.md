# Pure Finite-Dimensional Common-Copy Endpoint

## Requested Statement Achieved

`NonScalarInvariantMass.arbitrary_mass_light_exterior_of_semisimple` now takes
an arbitrary group H, finite-dimensional complex vector spaces S/T and their
genuine common-copy representations s/t, semisimplicity of s, arbitrary invariant
symmetric complex-bilinear B on the current matter carrier, and dim S > dim T.
No norm, inner product, H topology, compactness, continuity, source/target
unitarity or target semisimplicity is required by this endpoint.

The current carrier remains `(Ten tensor S) + bar-five + (Ten tensor T)*`,
with the standard unbroken SM-cover action, factorized common residual copy
actions and a scalar character psi on the untouched bar-five. “Arbitrary mass”
means every invariant symmetric mass on this carrier/action, not arbitrary
matter content or an arbitrary unrelated UV model. Source semisimplicity,
common-copy origin and positive dimension difference are the conditions retained
in the user's requested statement.

The conclusion derives three residual-equivariant species maps, exact equality
with B's mass form, membership of the actual participating quark/up-left/electron-left
ranges in B's radical, and nonzero SM/H/Lorentz/fermionic physical qque exterior
coefficient on those ranges. Right-handed up/electron use the existing actual
dual dictionary. No normal-form or light-placement certificate is supplied.

## Implementation

The [algebraic common-kernel proof](algebraic-copy-result.md) is unchanged.
`NonScalarCopyMass` and `NonScalarInvariantMass` previously carried unnecessary
norm/inner-product interfaces through their structural sections. Those sections
now use only `AddCommGroup`, `Module complex` and `FiniteDimensional` for S/T.
The tensor matter construction, injective equivariant embeddings, mass-form
reconstruction, derived residual-equivariance, actual radical memberships and
physical range transport are checked with those purely algebraic inputs.

Existing compact/continuous/unitary endpoints are in separate analytic sections
with their own metric/topology interfaces. Their proof consumers still build;
no Hilbertization or new metric certificate is inserted into the algebraic
endpoint. This strengthens the existing named theorem rather than adding a
parallel theorem on a surrogate carrier.

## Subsequent Model Abstraction

[The shared physical bridge](model-independent-result.md) removes the fixed
SU(5) carrier from the reusable implication. Actual mass squares are an explicit
model interface, and SU(5) derives this interface for every invariant B using
the normal form described above. Other models can reuse the implication after
proving their own realization; no universal matter classification is inferred.

## Remaining Boundaries

There is no residual analytic action premise to remove from the requested
endpoint. Source semisimplicity remains an explicit premise; it is not inferred
from finite dimension. Independent species representations, additional matter
irreps, the dim S ≤ dim T regime, full-light coefficient transport, global
quotient descent, UV residual mechanisms and all-BNV protection are outside
this statement. Nonzero allowed coefficient space does not imply UV matching
generates a Wilson coefficient or a proton decay rate.

See the [frozen plan](algebraic-carrier-plan.md),
[remaining connections](remaining-general-connections.md) and
[verification](verification.md). Strict audits and focused/full builds include
both the broadened algebraic interfaces and the retained analytic consumers.
