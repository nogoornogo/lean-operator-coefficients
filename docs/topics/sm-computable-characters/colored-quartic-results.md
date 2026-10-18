# Quartic kernels and the split top column

This page records checkpoint `checkpoint 01`. The subsequent
[two-component proof](colored-quartic-two-results.md) completes the generic
quartic Cauchy decomposition and identifies the top-column kernel.
Retained Q color/weak resolution remains open.

At this checkpoint the two proposed
kernel labels now have actual natural quotient maps and complete auxiliary
source splits. The first quartic constituent has an actual equivariant
split embedding. No numerical rank/multiplicity certificate, Weyl input,
new external premise or changed dependency is used.

## Actual multiplication kernels

[ExteriorFourthKernels](../../../Math/LinearAlgebra/ExteriorFourthKernels.lean)
constructs

```text
m13 : A tensor Lambda^3 A -> Lambda^4 A,
m22 : Sym^2(Lambda^2 A) -> Lambda^4 A.
```

For m22 the wedge of two two-forms is proved symmetric, using the proved
graded commutation identity in the exterior algebra. It then descends
through the actual symmetric quotient. Both maps send a pure four-vector
expression to the same fourfold exterior product.

The coproducts are obtained by alternatizing
`a tensor (b wedge c wedge d)` and
`sym((a wedge b) tensor (c wedge d))`. Mathlib's general theorem for
alternatizing an already alternating map proves that multiplication after
either coproduct is `4!` times the identity. The proof retains the symbolic
permutation sum; it does not enumerate a representation basis or a table
of coefficients. The scalar 24 is a universal alternator normalization,
not a content rank or multiplicity.

Normalized sections give

```text
A tensor Lambda^3 A = Lambda^4 A + K211(A),
Sym^2(Lambda^2 A)    = Lambda^4 A + K22(A).
```

Here both kernels are defined from the constructed maps. Explicit
projections and forward/inverse maps prove these **auxiliary** decompositions.
[SectionKernel](../../../Math/LinearAlgebra/SectionKernel.lean) factors out
the elementary right-inverse/kernel construction.
[Representation wrappers](../../../Math/RepresentationTheory/ExteriorFourthKernels.lean)
prove equivariance of the multiplication maps, coproducts, projections and
splits for an arbitrary group representation. No finite dimension,
irreducibility or supplied branching rule is required for these splits.

## An actual quartic constituent

[ExteriorFourthColumn](../../../Math/LinearAlgebra/ExteriorFourthColumn.lean)
constructs a retraction of the existing column map

```text
Lambda^4 A tensor Sym^4 B -> Lambda^4(A tensor B).
```

The retraction is an alternatized regrouping map divided by `4!`.
On pure symmetric powers the two permutation signs cancel, by a universal
identity for any permutation. The retraction composed with the column is
the identity. This proves injectivity and a complete split of the **top
column and its remaining kernel**. It applies to arbitrary A and B;
finite dimension and the doublet hypothesis are not needed.
[Its representation version](../../../Math/RepresentationTheory/ExteriorFourthColumn.lean)
retains both group actions and supplies an actual equivariant split.
[TensorFourthMultilinear](../../../Math/LinearAlgebra/TensorFourthMultilinear.lean)
provides the associated tensor/multilinear maps used in the construction.

## Symbolic exhaustion identity

[ExteriorFourthDimensions](../../../Math/LinearAlgebra/ExteriorFourthDimensions.lean)
derives the two kernel dimension relations from the proved auxiliary
splits. If n is the arbitrary dimension of A, k that of K211 and l that
of K22, they imply

```text
5 * choose(n,4) + 3*k + l = choose(2*n,4).
```

This is proved as a polynomial identity in the dimension parameter, using
general exterior/symmetric dimension formulas. No dimension is evaluated
at a particular SM content. `candidate_dimensions` proves equality of the
actual proposed three-branch carrier dimension with the quartic exterior
dimension for any two-dimensional B. `surjective_of_injective` records
the resulting exhaustion step **for a supplied linear map whose
injectivity has been proved**. It does not supply that map or its
injectivity.

## Obligations remaining at this checkpoint

The remaining kernel of the proved column retraction has not been
identified with `(K211(A) tensor Sym^2 W) + K22(A)` for a doublet W.
Actual maps for these two components and their joint independence remain
required. Equality of dimensions alone does not prove that equivalence.
The existing finite summand cancellation theorem cannot fill the gap
without an actual comparison of the remaining sources.

After that equivalence, retained color/weak resolution for A = color
tensor weak is still needed. Q degrees four through six and the original
complete mixed q/l support classification remain open. The definitions of
the kernels and the top-column complement must not be cited as that
classification. This is a verified checkpoint of the
[quartic plan](colored-quartic-plan.md), not a completed quartic endpoint;
see [verification](colored-quartic-verification.md).
