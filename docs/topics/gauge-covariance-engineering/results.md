# Proved Gauge Covariance, Trace IBP And Scalar Degree Two

## Algebraic Local Gauge Formulas

For the retained associative ordinary differential algebra, take an actual
unit `u`, its inverse `v`, and any connection. No derivative-constant condition
is imposed. The transformed connection is

\[
A'_i=uA_iv-(\partial_i u)v.
\]

The inverse derivative formula is derived from `uv = vu = 1`. It gives actual
covariant derivative, curvature and signed source-free EOM identities

\[
\nabla'_i(uxv)=u(\nabla_i x)v,\quad
F'_{ij}=uF_{ij}v,\quad E'_j=uE_jv.
\]

Identity and composition are proved; applying `u` then `w` gives the transform
by `wu`. Curvature covariance is derived using commuting ordinary derivatives,
not supplied as an input. A polynomial two-by-two unit with off-diagonal entry
`phi` has a nonzero derivative. Transforming the zero connection produces a
nonzero component `-partial_0 phi` and retains zero curvature.

The actual matrix jet consumer specializes these identities. Transformed
EOM entries lie in the existing full differential ideal and vanish under its
projection. Traces of squared curvature components are invariant under these
unit transformations. This does not construct a local gauge action by
automorphisms on the fixed connection-only polynomial ring or a quotient of
all local gauge orbits. A unit internal to the specified differential algebra
is the exact transformation parameter.

## Trace IBP In The Actual Quotient

For finite matrices over a commutative complex differential algebra, trace
cyclicity gives zero trace for commutators. Entrywise ordinary derivatives
commute with the trace. Therefore

\[
\mathrm{tr}((\nabla_i X)Y)+\mathrm{tr}(X\nabla_iY)
=\partial_i\mathrm{tr}(XY).
\]

The right side belongs to the actual ordinary divergence range. The identity
descends to the parent's linear EOM/IBP quotient for any polynomial seed set,
including the actual matrix Yang–Mills equations. Both trace terms become
negatives of each other. The parent's inverse source/coefficient comparison
continues to apply; IBP is not ideal-closed and its classes are not multiplied.
Trace conjugation invariance is proved for all internal units.

## Engineering Degree

Every component has engineering dimension one and every ordinary derivative
adds one. A jet variable with multi-index `a` has weight `1 + order(a)`.
`JetEngineering` proves that products add weighted degrees and total
derivatives raise degree by one. For finite component/direction sets, each
fixed degree contains finitely many monomials and is finite-dimensional.
Its EOM and full EOM/IBP image spaces are finite-dimensional for arbitrary
equations, without assuming a global quotient direct-sum decomposition.

The actual polynomial scalar seed has degree three. The matrix connection,
curvature and Yang–Mills equation have degrees one, two and three respectively.
For a homogeneous matrix expression, the actual covariant derivative raises
degree by one. These weight statements are proved on the actual sources,
not inferred from displayed physical dimensions.

## Complete Four-Dimensional Scalar Consumer

For every complex `lambda`, retain the full equation
`box phi + lambda * phi^3` and all its descendants. The complete off-shell
engineering-degree-two source is spanned by

\[
\phi^2,\quad \partial_0\phi,\quad\partial_1\phi,
\quad\partial_2\phi,\quad\partial_3\phi.
\]

Finite monomial reconstruction proves that no other source is omitted. The
four first jets vanish in the actual divergence quotient. To prove that the
remaining square survives **all** unbounded EOM and IBP relations, evaluate
the undifferentiated field at a polynomial variable `t` and all positive jets
at zero. All ordinary derivatives evaluate to zero; the seed evaluates to
`lambda * t^3`. Thus the entire differential ideal maps into `(t^3)`.
Taking the coefficient of `t^2` annihilates that ideal and every divergence,
and takes value one on `phi^2`.

This gives reconstruction, an inverse coordinate equivalence with the complex
line, a singleton basis and exact dimension one for the degree-two image in
the **full** EOM/IBP source, for every `lambda`, including zero. No truncation
of relations or external relation matrix is used. This is one scalar sector;
it is not a general Yang–Mills invariant basis or a classification at other
engineering degrees.

## Successful Stop And Retained Boundaries

All three stages of the [contract](plan.md) are proved and their acceptance
gates are recorded in [verification](verification.md). Lagrangian derivations
and formal first variations remain deferred as instructed. Analytic fields,
local gauge orbit quotients, SU(N) real/traceless restrictions, a matrix-model
Lorentz dictionary, mixed nonlinear fermionic equations, general normal forms
or operator counts, amplitudes, matching, RGE and numerical dynamics remain
separate scope decisions. The verified child remains unmerged into its parent.
