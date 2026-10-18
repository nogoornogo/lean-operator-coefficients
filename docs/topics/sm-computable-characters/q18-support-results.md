# Q18 support without numerical evaluation

The user approved changing the Q18 endpoint from exact multiplicity/rank
numerals to actual zero/nonzero support. The following statements implement
the [plan](q18-support-plan.md); the old exact equalities are preserved as
[archived source records](archive/q18-numerical/README.md).

## Proved actual support

[SMQ18LocalSupport](../../../Physics/StandardModel/Operators/SMQ18LocalSupport.lean)
uses the positive Q species, three generations, a constant 18-field content
and the existing trivial residual action. For every even m <= 18 at delta -6:

- `local_allowed` supplies a nonzero actual local gauge/Weyl invariant
  coefficient, including the exterior-statistics constraint;
- `kernel_allowed` supplies a nonzero element of the actual finite constraint
  kernel, and `kernel_positive` proves its dimension is positive;
- `rank_deficient` proves the actual constraint rank is smaller than the
  actual carrier dimension, with both quantities left symbolic;
- `q18` specializes to the former numerical test's m=6, delta=-6.

These statements require no Weyl torus-reduction input, assumed multiplicity,
character table, numerical rank certificate or new literature premise. They
do not assert the retired exact multiplicity or rank numbers. The fields,
chirality, independent spin factors and hypercharge convention are the same
as the original case. Nonzero coefficient support is not a generation or
rate claim. Original Higgs degrees still require their existing constituent
admissibility condition; the uniform constituent statement does not remove it.

## Construction

[SMQ18Support](../../../Physics/StandardModel/Operators/SMQ18Support.lean)
proves the semisimple Q field has dimension 36 and determinant-one action.
The perfect pairing between complementary exterior powers therefore makes
degree 18 self-dual. The already proved injective weak constituent map,
composed with this duality and the dual map, yields an invariant functional.
Dual separation proves it is nonzero. No basis of the degree-18 exterior
space is enumerated. Choosing a top volume by `Module.finBasis` remains a
noncomputable mathematical choice; it is never evaluated as a coordinate list.

[SelfDualCoefficient](../../../Math/RepresentationTheory/SelfDualCoefficient.lean)
and [FactoredInvariantSupport](../../../Math/RepresentationTheory/FactoredInvariantSupport.lean)
prove the generic coefficient and group-extension steps with representations
kept as parameters. [SMCombinedChargeSupport](../../../Physics/StandardModel/Operators/SMCombinedChargeSupport.lean)
proves the scalar action and factorization for arbitrary content. The Q18
consumer restores U(1) using its actual charge cancellation, then applies
the existing combined-compact/local/kernel equivalences. An analytic Hom
reversal or evaluated character integral is not needed for this middle degree.

The source equivalence is proved at arbitrary exterior degree. Its
intertwining proof uses an equality of linear operators, avoiding transport
of a large dependent source type through an equality of representations.
Likewise scalar action and invariant extension are proved generically before
specialization. No heartbeat, recursion or memory budget was increased.

## Boundary

This closes the approved Q18 nonzero case and the stated even-m family.
It is not the full arbitrary-m Q18 support iff: the remaining necessary weak
parity condition is not included here. The existing sharp-bound theorem
already forbids m > 18; charge compatibility is retained by the original
interfaces. Other Q/L degrees, conjugate species and the full q/l/Higgs
classification remain under the [structural continuation](structural-results.md).
No CSV cells or the status of the numerical rank classifier are changed.

[Verification](q18-support-verification.md) distinguishes focused support
checks from any remaining full-project build boundary.
