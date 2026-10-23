# Finite-Group Spurion Evaluation

For a finite group H and finite-dimensional complex representations S and W,
every vector fixed by the actual stabilizer of a specified s is the value of
a polynomial H-covariant:

$$
\mathrm{ev}_s:\mathrm{Poly}_H(S,W)\longrightarrow W^{H_s}
\quad\text{is surjective},\qquad H_s=\{g\in H\mid gs=s\}.
$$

There is no genericity, faithfulness or nonzero-value hypothesis. Source and
target use finite coordinate sets; choosing bases gives this presentation for
finite-dimensional spaces. Polynomial data are holomorphic, of finite degree
for each witness. The bounded version below gives an explicit sufficient cutoff.

## Construction And Declarations

[FiniteGroupPolynomialEvaluation](../../../../../Math/RepresentationTheory/Constructions/FiniteGroupPolynomialEvaluation.lean)
proves `finite_interpolation` on arbitrary finite sets of coordinate vectors.
For w fixed by H_s, `orbit_factors` makes hs -> hw well-defined on the orbit.
Interpolate that finite orbit data, then average:

$$
R(x)=\frac{1}{|H|}\sum_{g\in H} b(g^{-1})P(a(g)x).
$$

`reynolds_covariant` proves the covariance law, and
`finite_group_surjective` proves R(s)=w. Linear substitutions are constructed
as actual coordinate polynomials; no polynomial-extension or saturation
premise is supplied to the final theorem.

## Residual Coefficient Consumer

[FiniteGroupSpurionCoefficients](../../../../../Math/RepresentationTheory/Spurions/FiniteGroupSpurionCoefficients.lean)
uses a supplied residual representation r on Q. The contragredient convention
is (g f)(q)=f(g^{-1}q). `fixedDualEquiv` identifies the fixed dual space with
`IntertwiningMap (r.comp H_s.subtype) (trivial ℂ H_s ℂ)`.
`coefficientEvaluation_surjective` therefore proves

$$
\mathrm{Poly}_H(S,Q^*)\longrightarrow\mathrm{Hom}_{H_s}(Q,\mathbb C)
\quad\text{is surjective}.
$$

`finite_dimensional_coefficients` chooses dual coordinates by a finite basis.
`coordinate_stabilizer` proves that source-coordinate transport preserves the
actual stabilizer. `nonzero_coefficient_iff` gives the corresponding nonzero
existence criterion.

The target is the same residual-Hom interface used by
[graded completeness](GRADED_OPERATOR_COMPLETENESS.md); set r to the supplied
content quotient action. This does not prove that every quotient in the
general theorem is finite-dimensional. The new finite-coordinate hypothesis
belongs to this consumer and does not constrain the existing general theorem.
No new quotient, field-statistics rule or content decomposition is introduced.

## Finite Total-Degree Cutoff

[FiniteGroupSpurionDegree](../../../../../Math/RepresentationTheory/Spurions/FiniteGroupSpurionDegree.lean)
strengthens evaluation surjectivity to a finite spurion-degree cutoff:

$$
D_s=|H\cdot s|-1\leq |H|-1,\qquad
\mathrm{ev}_s:\mathrm{Poly}_{H,\leq D_s}(S,W)\longrightarrow W^{H_s}
\quad\text{is surjective}.
$$

`DegreeLE p d` bounds the total degree of every coordinate of p by d.
`boundedCovariants` is a linear subspace of the existing covariants;
`boundedEvaluation` restricts the existing evaluation map to that subspace.
`boundedEvaluation_surjective` proves the orbit-size bound, and
`card_boundedEvaluation_surjective` gives the group-order bound.

The proof chooses separating polynomials of degree at most one, multiplies
at most one per other orbit point, and interpolates without increasing that
bound. `totalDegree_bind_linear` proves that substitution by linear
polynomials cannot increase total degree. Target linear maps and Reynolds
averaging also preserve the bound. No degree bound is an input premise.

`boundedCoefficientEvaluation_surjective` and
`finite_dimensional_bounded_coefficients` give the same cutoff for the
residual-Hom consumer above; the group-order version is also proved.
The bound concerns spurion total degree, not operator engineering dimension,
finite generation, or a classification of minimal degrees for individual targets.

## Controls And Limits

[FiniteGroupSpurionExamples](../../../../../Math/RepresentationTheory/Spurions/FiniteGroupSpurionExamples.lean)
uses the permutation action on two complex coordinates. At a value with
distinct coordinates the stabilizer is trivial and every target is attained.
At zero every evaluation has equal coordinates; a constant invariant vector
is attained, while the same noninvariant vector attained at the free value
cannot be attained at zero. Thus the codomain must track the actual stabilizer.

[Degree controls](../../../../../Math/RepresentationTheory/Spurions/FiniteGroupSpurionDegreeExamples.lean)
prove that degree one suffices for every target at the free value of the
two-coordinate permutation example, while degree zero fails for a specified
target. At zero the orbit is a singleton and degree zero suffices for every
stabilizer-invariant target; a nonzero constant target is exhibited.

The [persistent audit](../../../../../Math/RepresentationTheory/Spurions/Audit/AuditFiniteGroupSpurionEvaluation.lean)
checks 29 declarations transitively against `propext`, `Classical.choice` and
`Quot.sound`, and excludes Physics/GUT imports. See the
[verification record](../../../../topics/finite-group-spurion-evaluation/verification.md).
The separate [degree audit](../../../../../Math/RepresentationTheory/Spurions/Audit/AuditFiniteGroupSpurionDegree.lean)
checks 28 additional declarations under the same strict policy and layer boundary.

This direct finite-group proof does not certify general continuous/algebraic
group saturation, a generic-locus theorem, finite generation,
or the MLFV scenarios of the motivating literature. No UV generation,
matching, rates, derivatives or IBP/EOM follow. See the
[source register](../../../../topics/finite-group-spurion-evaluation/references.md)
and [literature list](../../../RELATED_LITERATURE.md).
