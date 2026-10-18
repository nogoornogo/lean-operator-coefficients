# Complete Actual SM Local Finite Kernel

## Compact finite tests

[IntegralTorusTests](../../../Math/RepresentationTheory/IntegralTorusTests.lean)
uses the exact circle element `Circle.exp 1`. Irrationality of pi proves that
its integer powers are injective. Consequently one test at this element is
exhaustive for circle invariance whenever integral torus eigenvectors span the
representation. The result is algebraic: it assumes no continuity or density,
and it is stable under surjective intertwining maps, tensor products and fixed
conjugation of the circle.

[TwoCircleGeneration](../../../Math/LieGroups/SpecialUnitary/TwoCircleGeneration.lean)
constructs one fixed matrix `mix` and proves an explicit
diagonal/rotation/diagonal factorization of every actual SU(2) matrix. The
rotation circle is the conjugate of the diagonal circle by `mix`. Thus the two
tests at the exact infinite-order sample are exhaustive on every representation
whose diagonal-torus integral eigenvectors span.

[ColorPlaneCircles](../../../Math/LieGroups/SpecialUnitary/ColorPlaneCircles.lean)
embeds this SU(2) into the 01, 02 and 12 coordinate planes of actual SU(3).
It connects those embeddings to the previously proved three-plane reduction.
The two circle tests in each plane give six exhaustive color tests. Together
with the two weak tests and one hypercharge-circle test, the compact family has
9 labels. The persistent Math audit checks the dependency layer and 24 strict
transitive axiom closures.

## Actual statistical carrier

[SMColorIntegralBasis](../../../Physics/StandardModel/Operators/SMColorIntegralBasis.lean)
constructs exact color-torus basis weights for all ten signed SM species,
including the dual species. These weights propagate through Weyl and flavor
bases, finite tensor products and the actual statistical exterior image by its
surjective intertwiner. No ordered-tensor support is substituted for the
statistical source.

[SMIntegralLocalWeights](../../../Physics/StandardModel/Operators/SMIntegralLocalWeights.lean)
combines those color weights with the existing weak source weights and exact
hypercharge action. It separately proves integral torus spanning for the
source and the Higgs constituent, then for their tensor action. The Higgs weak
weights are the actual symmetric-power weights; its hypercharge weight is
`3*delta`. Residual flavor is evaluated at identity and otherwise remains an
arbitrary supplied representation.

## Full finite matrix and q/l support

[SMFullLocalKernel](../../../Physics/StandardModel/Operators/SMFullLocalKernel.lean)
joins the compact tests to the previously certified four real Weyl
transvection families sampled at `0,...,n`. For a content word of length n,
the complete actual-local family has

    9 + 4*(n+1)

labels. `exhaustive` proves invariance under these tests iff the coefficient is
invariant under every element of
`GaugeGroup x WeylSpinor.Group`. With a classical finite basis of carrier
dimension D, `matrix` has columns indexed by D and rows indexed by the test
labels times D. Its entries are the exact coordinates of `rho(g)b_j-b_j`.
`coefficientEquiv` identifies the actual invariant coefficient space with the
kernel of this matrix, and `allowed_iff_rank_lt` identifies nonzero support
with its exact rank being smaller than the number of columns.

[SMQLFullKernel](../../../Physics/StandardModel/Operators/SMQLFullKernel.lean)
composes that equivalence with the already proved scalar q/l residual
separation and all-degree Higgs reduction. For arbitrary positive cyclic order,
q,l, content p and Higgs degrees h,d, `original_allowed_iff` proves

    Allowed(original q/l coefficient space)
      iff total q/l charge = 0
      and there exists an admissible bounded weak degree m
      whose explicit local constraint matrix has rank below its column count.

`test_allowed_iff` gives the corresponding statement for every retained
finite-table test. Thus the requested existing q/l support classification has
no residual invariant-Hom `Allowed(T)` term, polynomiality premise or supplied
exhaustiveness premise.

The result is an exact finite-rank characterization. Its classical basis and
complex coefficients do not provide an executable rank algorithm; see the
[rank evaluation boundary](../sm-rank-enumeration/results.md). It does not
classify new residual action classes, add Higgs
copies or derivatives, or establish masses, UV realization, matching or rates.
The 572 q/l assignment recount is also outside this endpoint.
