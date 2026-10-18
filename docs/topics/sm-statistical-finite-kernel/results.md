# Actual Statistical Weyl Kernels And Compact Follow-Up

## Stage 2: actual Weyl statistical sampling proved

[AffineStatisticalSampling](../../../Math/RepresentationTheory/AffineStatisticalSampling.lean)
uses scalar functional orbit polynomials instead of constructing a separate
vector-polynomial module. This is sufficient for coefficient invariance and
avoids a new polynomial-module foundation. `multilinear_affine` explicitly
expands an affine action on each slot over all subsets of slots: the exponent
is the subset cardinality, so the degree is at most the slot count.
`raw_polynomial` extends this to arbitrary ordered tensor vectors by linearity.
`descend` transports degree certificates through a supplied surjective
intertwiner, and `statistical_source` discharges that interface with the actual
`PatternExteriorSource.onto` and its proved surjectivity. No statistical-image
or quotient-polynomial premise remains for this consumer. `tensor_fixed`
retains the same degree when the other tensor factor is fixed.

[WeylRealTransvections](../../../Physics/FieldTheory/Spinor/WeylRealTransvections.lean)
defines four actual families: upper/lower off-diagonal pairs, each with a real
or imaginary parameter. `split_transvection` proves that an arbitrary complex
transvection is the product of its real and imaginary versions. `generates`
therefore discharges algebraic generation for actual SL(2,C). `spinor_affine`
proves the actual left and entrywise-conjugate-right actions are affine in the
same real parameter. It does not introduce two independent chiral groups.

[SMWeylFiniteKernel](../../../Physics/StandardModel/Operators/SMWeylFiniteKernel.lean)
proves the field identity for all ten actual signed species, with the fixed
three-generation carriers and arbitrary residual flavor representations.
`source_polynomial` propagates it through the actual content-statistical image
for **every** species word of degree n. Higgs constituents are fixed by Weyl,
so `action_polynomial` proves degree at most n on their tensor product with
the statistical source, for every m and delta.

The samples are exactly the real natural numbers 0,...,n. The difference from
an invariant value is also degree at most n, so n+1 distinct complex images
force the residual polynomial to be zero. There are 4(n+1) test labels (some
labelled elements are redundant). `exhaustive` proves these explicit tests
are exhaustive for actual Weyl invariance on every such statistical carrier.
No polynomiality, degree or exhaustive-test premise remains in this actual
SM Weyl theorem. It also covers n=0 and zero statistical carriers.

## Stage 3: exact partial connection proved

`SMWeylFiniteKernel.coefficientEquiv` is an actual Weyl-invariant coefficient /
finite kernel equivalence. `allowed_iff_rank_lt` is the corresponding Weyl-only
rank criterion. A finite basis can be supplied, or `basis` constructs one
using the actual carrier's proved finite dimension; `canonicalEquiv` supplies
this classical basis. Matrix entries remain the existing exact coordinates
of rho(test) minus identity, with orientation and inverse maps certified.
No matrix entries or ranks have been enumerated computationally.

[PartialInvariantKernel](../../../Math/RepresentationTheory/PartialInvariantKernel.lean)
proves the product-factor connection: finite rows for one factor together
with the **explicit actual invariance conditions for the other factor** are
linearly equivalent to full product-group invariant coefficients.
Its `Space` is a submodule of the finite coordinate space, not merely the
Weyl kernel and not a claimed fully finite constraint system.

[SMQLPartialKernel](../../../Physics/StandardModel/Operators/SMQLPartialKernel.lean)
discharges the Weyl exhaustive premise for the actual local gauge/Weyl action.
`coefficientEquiv` identifies the existing q/l `LocalTest` with the finite Weyl
kernel subject to actual gauge invariance. `original_allowed_iff` composes
this with the original statistical/Higgs coefficient connection: q/l charge
neutrality and a bounded Higgs-constituent index, with support tested on that
partial coordinate space. Hypercharge remains part of actual gauge invariance;
no new charge assumptions or residual action class are introduced.

## Compact routes and subsequent discharge

Stage 1's actual SU(3) plane generation is already proved. Its plane SU(2)
parameters remain infinite and constrained by normalization. Finite sampling
of those parameters and the weak SU(2) factor is still missing.

The two recorded routes were inspected once:

- Circle factors: pinned TauCeti SU2 Basic provides a diagonal torus;
  Weyl/Basic proves generation of its **normalizer**, and TorusConjugacy
  proves conjugacy into the torus with an arbitrary group conjugator.
  None is a fixed finite circle-family generation certificate for all SU(2).
  Such a certificate is required before a bounded Laurent weight test can
  replace actual SU(2) invariance. Torus conjugacy of class functions is not
  exhaustiveness for arbitrary coefficient functionals.
- Rational coordinates: existing local SphereSection supplies actual
  unitary/special-unitary local sections and patch coverage. These are not
  a certified rational parameter family for the chosen SU(2) plane blocks
  with bounded polynomial numerators and controlled nonzero denominators.
  The exact real coordinate coverage (including excluded points), denominator
  clearing through dual/statistical actions and multivariate sampling are
  separate obligations. The scalar affine interface does not establish them.

[AffinePairBoundary](../../../Math/LieGroups/SpecialUnitary/AffinePairBoundary.lean)
proves a concrete obstruction to directly reusing the Weyl affine route:
normalized complex pairs at affine parameters 0,1,-1 already force both
linear coefficients to vanish. `actual_row` applies this to actual SU(2) rows.
This is not an obstruction to rational or Laurent finite sampling.

This checkpoint originally stopped at the separate actual SU(2) fixed-circle
generation certificate. The authorized
[compact-kernel follow-up](../sm-compact-kernel-completion/results.md) now proves
that certificate by an explicit Euler factorization, supplies finite color,
weak and hypercharge tests, and combines them with the Weyl rows here. The
checkpoint's own partial equivalence remains useful, while the follow-up is
the full gauge/Weyl finite-rank classifier for the existing q/l consumer.
