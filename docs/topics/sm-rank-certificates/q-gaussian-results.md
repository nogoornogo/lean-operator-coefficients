# Constant-Q support from exact coordinate polynomials

The constant-Q/conjugate-Q endpoint is proved by a variant of Route B.
The degrees n,m and the hypercharge index delta remain symbolic. The result
constructs an explicit Gaussian-rational matrix family and proves its equality
with actual coefficient constraints. A characteristic-polynomial formula then
gives the actual nullity and a finite local support predicate. No separate
rank certificate for an individual degree, unproved spanning premise or
numerical matrix entry is an input to the final theorem.

The family retains three flavors, the actual statistical exterior source,
the actual gauge and paired Weyl groups, and one-doublet Higgs constituents.
Supplied residual actions are evaluated at the identity for local counting.
The result is complete for the constant Q/conjugate-Q local family; it does
not classify mixed species or residual selection.

## Explicit formula

Let K be mathlib's quadratic algebra `QuadraticAlgebra ℚ (-1) 0`, embedded in
complex numbers by (a,b) ↦ a+b*i. Its field condition is proved from the fact
that a rational square is nonnegative. Its conjugation is carried to complex
conjugation by the embedding.

Index the 36 Q basis slots by color × weak × Weyl × flavor. For each n,m,
use n-element subsets of these slots and unordered m-tuples of the two Higgs
basis labels. The Q exterior coefficient is a finite minor of the one-field
matrix. The Higgs coefficient is a finite sum of products of its two-dimensional
entries, averaged over all orderings of its input monomial. The number of
orderings is proved positive, and `symmetricFormula_eq` identifies this sum
with the actual symmetric-power coordinate. Thus the matrix construction
uses exact finite sums/products, minors and Gaussian rational arithmetic.

There are 9+4*(n+1) actual local tests: six color circle tests, two weak circle
tests, one hypercharge circle test, and the existing four real Weyl
transvection families sampled at the integers 0,...,n. The compact and
hypercharge tests use the exact infinite-order point (3+4*i)/5. The two-circle
mixing matrix, coordinate-plane embeddings and Weyl samples likewise have
explicit Gaussian-rational entries.

Let T_t be the resulting exterior/Higgs matrix and define

    A(n,m,delta)[(t,j),k] = T_t[k,j] - [k=j]
    P(n,m,delta)(X) = det(X*I - A(n,m,delta)^* A(n,m,delta)).

Both A and P are constructed over K. Their dimensions and entries are
specified by n,m,delta, without an actual complex coefficient space as input.
The proved statements in
[SMQGaussianKernel](../../../Physics/StandardModel/Operators/SMQGaussianKernel.lean)
are:

- `matrix_semantics`: embedding A into complex numbers gives the actual
  coefficient constraint matrix in the constructed exterior/monomial basis.
- `coefficient_dimension` and `kernel_dimension`: actual nullity equals
  `natTrailingDegree P`, the smallest exponent having a nonzero coefficient.
- `allowed_iff`: actual local coefficients exist iff `P.coeff 0 = 0`.
- `rank_add_nullity`: the rank of the original actual finite matrix plus this
  nullity equals `choose(36,n)*(m+1)`.
- `nullity_above_capacity`, `forbidden_odd` and `forbidden_charged`: the formula
  respects the independent capacity, Weyl parity and hypercharge tests.

P is a characteristic polynomial, hence monic and nonzero. The zero-column
case therefore has P=1 and is handled by the same formula. This is a symbolic
matrix-family formula, not dispatch over a table of fixed-degree results.
It retains a determinant computation; it is not an A2 weight-difference formula
or a proof that large numerical evaluation is efficient.

## Actual-group and field connections

[RationalCircleTests](../../../Math/RepresentationTheory/RationalCircleTests.lean)
proves infinite order using integrality: a root of unity and its inverse
would be algebraic integers, but their sum 6/5 is not integral over ℤ.
The existing integral-weight spanning theorems then prove that the new single
circle sample tests the whole circle. `RationalCompactTests` combines this
with the existing actual SU2 and SU3 generation proofs.

[SMRationalLocalKernel](../../../Physics/StandardModel/Operators/SMRationalLocalKernel.lean)
proves exhaustivity for the actual full local coefficient action.
`SMGaussianLocalData` supplies the exact matrices of every sample.
[SMQExactCoordinates](../../../Physics/StandardModel/Operators/SMQExactCoordinates.lean)
constructs the actual basis through `ConstantPatternExterior` and proves its
one-field, exterior and Higgs coordinates agree with the Gaussian formulas.
No rationality assumption on an arbitrary complex matrix is used.

`GramNullityPolynomial.nullity` uses the Hermitian spectral theorem and rank
of A* A to identify zero-root multiplicity with kernel dimension. Embedding
commutes with the Gram characteristic polynomial, and injectivity preserves
its support and lowest nonzero coefficient. This transports the complex
proof back to the exact K polynomial.

[SMQConjugateKernel](../../../Physics/StandardModel/Operators/SMQConjugateKernel.lean)
transports the entire conjugate-Q local coefficient space to Q with delta
reversed. Its dimension, support and original matrix rank therefore use
P(n,m,-delta). Existing gauge/Weyl conjugation and Higgs epsilon duality
supply the transport; residual flavor representations are not identified.

## Full Higgs degrees

[SMConstantFullSupport](../../../Physics/StandardModel/Operators/SMConstantFullSupport.lean)
connects these formulas to `SMFiniteHiggsSupport.OriginalSpace`, retaining
actual full-field statistics and the selected constant species content.
With the residual group fixed to Unit and the existing three-flavor trivial
input, `quark_allowed_iff` and `conjugate_quark_allowed_iff` cover arbitrary
h,d: there is a weak constituent m in the already proved finite source bound,
its `Admissible h d m` condition holds, and the appropriate P constant
coefficient vanishes at delta=h-d (with sign reversal for conjugate Q).
The corresponding two lepton theorems use their finite weight multiplicity
and exact neutrality condition. Thus no Higgs-degree cap is added and no
residual action condition is silently dropped from a nontrivial model.

## Route choice and completion boundary

The user authorized reopening stages 4--5 and switching routes. Inspection
of the pinned GL Weyl-module and Schur-Weyl results did not supply the needed
SU3/exterior extraction adapter, so Route B was used. The originally proposed
zero-weight compression was replaced here by a full explicit coordinate basis.
This preserves all constraints and allows a uniform symbolic nullity proof
without materializing a large matrix. Zero-weight compression remains an
optional computational optimization, not an unproved premise of this result.

The formal endpoint for the 107 formerly unresolved neutral constant-content
candidates is now covered: L/conjugate-L by the
[finite weight formula](lepton-multiplicity-results.md), Q/conjugate-Q by the
exact coordinate polynomial. The CSV and `SMConstantContentRanks.evaluate`
remain conservative and unchanged; this work has not evaluated or certified
new individual numerical table entries. In particular it does not assert a
practical dense-matrix computation at the largest degrees.

Route A's A2 constant-term theorem itself remains unproved. Mixed-content
support, the 572 q/l assignments and arbitrary residual invariant selection
remain separate endpoints. No dependencies, custom axioms, literature premises
or physical matching inputs were added. See [verification](verification.md).
