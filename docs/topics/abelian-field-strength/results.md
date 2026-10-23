# Free Abelian Maxwell/Bianchi Source

## Actual Lorentz-Covariant Equations

The component source is the actual tensor square of the existing four-vector
representation, transported through its tensor basis to sixteen ordered-pair
labels. Antisymmetry is imposed algebraically, not assumed as a rank or basis
premise. Every diagonal component and every symmetric pair, with all polynomial
derivative descendants, vanishes in the quotient.

For the metric signs `s = (1, -1, -1, -1)`, the equation families are

\[
A_{ab}=F_{ab}+F_{ba},\qquad
M_b=\sum_a D_aF_{ab},\qquad
B_{abc}=s_aD_aF_{bc}+s_bD_bF_{ca}+s_cD_cF_{ab}.
\]

These are source vectors in the repository's tensor/dual-direction convention.
Coefficient functionals live in the dual. In particular, the displayed labels
do not silently supply a dictionary to classical raised/lowered field columns.
The field-strength model is complexified, free and source-free, with ordinary
commuting derivatives and signature (+---).

The actual equation representation is a product of a tensor square, a vector
and a tensor cube. The antisymmetry, Maxwell and Bianchi seed maps intertwine
these with the existing combined jet action. Metric intertwining follows from
polarization of the proved Pauli quadratic invariance. Maxwell covariance uses
the canonical vector/dual identity, and Bianchi covariance uses that metric
bridge. No equation covariance or relation stability is an external premise.

The combined linear seed feeds the existing full polynomial-descendant closure.
Quotient shifts commute, the group action descends, and every displayed seed
and descendant vanishes. The scalar wave equation is a consequence:

\[
(D_0^2-D_1^2-D_2^2-D_3^2)F_{ab}=0.
\]

Its proof differentiates and sums Bianchi, uses antisymmetry and both relevant
Maxwell contractions, and transports the result to every polynomial descendant.
The wave equation is not substituted for the first-order Maxwell/Bianchi system.

## Retained Jets And Actual Algebra

At the null symbol `p = (1, 0, 0, 1)`, use the raised vector
`u = (1, 0, 0, -1)` and transverse polarizations `a = e₁, e₂`. The alternating
amplitude `uᵢaⱼ - aᵢuⱼ`, multiplied by polynomial evaluation at `p`, gives two
linear probes on the actual jet source. Both annihilate antisymmetry, Maxwell,
Bianchi and all descendants. Their induced quotient maps detect the classes
`D₀ᵏ F₀₁` and `D₀ᵏ F₀₂` by the identity matrix for every `k`. Hence these two
classes are independent and nonzero at every order before IBP. This is not a
classification of all polarizations, an exact helicity count or an analytic
plane-wave solution theorem.

With an empty odd species set, the common linear EOM algebra constructs the
actual symmetric algebra on these quotient generators. Its mixed presentation
is explicitly algebra-equivalent to that symmetric algebra: the empty odd
factor is proved equivalent to the scalar algebra. The presentation has an
onto projection from the off-shell algebra; the kernel is exactly the
two-sided ideal of all equation descendants. The induced even derivatives
intertwine that projection. Scalar-valued algebra probes retain the displayed
jets in this actual algebra before IBP as well.

Every fixed field/derivative image grade is finite-dimensional. The actual
divergence range gives inverse equivariant comparison between EOM followed by
IBP and the off-shell projection kernel plus IBP range. The invariant coefficient
descent is instantiated for the actual Lorentz action, without averaging that
group or assuming an invariant rank table. No product on IBP classes is asserted.

## Scope And Source Map

The [frozen contract](plan.md) is fulfilled within the exact symbolic source
model. There is no potential/gauge-quotient exactness theorem, Poincaré lemma,
non-Abelian extension, interacting/source term, analytic dynamics, Physlib
Maxwell equivalence, Hodge/helicity classification, general EFT operator table,
amplitude or physical rate result. Nonzero source jets are controls before IBP;
no surviving Lorentz-invariant integrated interaction is inferred.

- [Tensor and metric bridge](../../../Physics/FieldTheory/Jets/AbelianFieldStrength.lean).
- [Combined equation and actual covariance](../../../Physics/FieldTheory/Jets/MaxwellLinearEquation.lean).
- [Coordinate equations and wave consequences](../../../Physics/FieldTheory/Jets/MaxwellWave.lean).
- [Transverse quotient probes](../../../Physics/FieldTheory/Jets/MaxwellProbes.lean).
- [Actual algebra, kernel and EOM/IBP descent](../../../Physics/FieldTheory/Jets/MaxwellIBP.lean).
- [Strict audit](../../../Physics/FieldTheory/Jets/Audit/AuditMaxwellLinearEquation.lean).
- [Proof dossier](../../proof/current/core/Physics/ABELIAN_FIELD_STRENGTH_IBP.md),
  [sources](references.md) and [verification](verification.md).
