# Finite Scalar Completeness Results

The bounded C1/C2 targets are complete across this topic and its
[order-four successor](../scalar-quartic-four-completeness/results.md).
The successor closes the former C2 order-four invariant-coefficient gap and
is integrated into master. Its [literature verification](../scalar-quartic-four-completeness/literature-validation.md)
and [integration evidence](../scalar-quartic-four-completeness/integration.md)
own that added result. The original construction and failed-route evidence
below are retained as checkpoint history, not outstanding proof obligations.

The [frozen contract](plan.md) uses the unbounded actual jet sources and
the complete free differential EOM ideal plus the linear divergence range.
No paper coefficient, Python rank or invariant-extension premise is used.

| Sector | Lean result | Scope |
| --- | --- | --- |
| C1, content (1,1), derivative order 1 | Actual quotient image and admitted coefficient space are each a complex line. | Complete actual selected source. |
| C1, content (2,2), orders 1 and 2 | Actual quotient image and admitted coefficient space are each a complex line in both sectors. | Complete actual selected sources. |
| C2, four identical fields, order 2 | Every admitted Lorentz-invariant coefficient is zero; coefficient dimension 0. | Complete actual grade, not only the kinetic representative. |
| C2, four identical fields, order 4 | K-squared evaluation is a linear equivalence from the entire selected invariant coefficient space to the complex numbers, with normalized inverse and dimension 1. | Completed by the [successor](../scalar-quartic-four-completeness/results.md); the full un-invariant quotient is larger than the candidate line. |

## C1: source reconstruction and independent coefficients

[ScalarFirstJetReduction](../../../Math/Algebra/ScalarFirstJetReduction.lean)
maps all unbounded jets to four variables phi,phi',chi,chi'. Its derivation is
phi' partial_phi + chi' partial_chi. Derivative compatibility proves that the
whole differential EOM ideal maps to zero. Explicit normalized coefficient
functionals also kill every ordinary total derivative. Their annihilation is
on the entire source, not only the inspected finite grade.

[ScalarTwoSpeciesCompleteness](../../../Math/RepresentationTheory/ScalarTwoSpeciesCompleteness.lean)
classifies every monomial in the three selected grades, proves EOM/IBP
reconstruction and provides actual-image and coefficient linear equivalences
with the complex numbers. Both inverse laws are part of these equivalences;
`first_extraction` and `second_extraction` identify coefficient evaluation.
The global coefficients realize any prescribed complex value on the selected
representative. No selected coefficient extension is assumed.

Together with the predecessor's d=0 results and complete (1,1),d=2 vanishing,
the bounded C1 coefficient lists at orders 0,1,2 are (1,1,0) and (1,1,1) for
contents (1,1) and (2,2). These agree with the corresponding expansion of
[1507.07240v1 Eq. (3.11)](https://arxiv.org/pdf/1507.07240v1), PDF p. 13.
This is a finite comparison, not a proof of the whole series or arbitrary
positive-degree contents. The complexified commuting species have no
spacetime or internal symmetry in this one-direction example; the paper's
auxiliary SL(2,C) counting construction is not a Lorentz action here.

## C2 order two: actual Lorentz coefficient vanishing

[ScalarDegreeTwo](../../../Math/Algebra/ScalarDegreeTwo.lean) proves exhaustive
monomial coverage in the unbounded four-field/two-derivative grade: phi cubed
times a second jet, or phi squared times two first jets. The direction type
is arbitrary in this helper; no twenty-row list is a premise.

[LorentzFiniteControls](../../../Physics/FieldTheory/Jets/LorentzFiniteControls.lean)
constructs two sign flips and the real/imaginary unit shears as actual
SL(2,C) elements and proves their direction matrices. Applied to an invariant
bilinear form, the flips kill off-diagonal entries and the shears force the
Minkowski diagonal proportions. The free EOM/IBP trace identity kills the
remaining value.

[ScalarQuarticTwoCompleteness](../../../Physics/FieldTheory/Jets/ScalarQuarticTwoCompleteness.lean)
uses this on every admitted selected coefficient. Leibniz IBP then kills the
second-jet monomials, so `selected_forbidden` and `coefficient_dimension`
hold on the entire grade. An ordinary linear extension is used only to
write a selected coefficient on polynomials; invariance and relation
annihilation are proved only where needed in the selected grade. No
invariant or relation-preserving extension is presumed.

## C2 order four: original separation and reduction checkpoint

[FourWaveEvaluation](../../../Math/Algebra/FourWaveEvaluation.lean) proves
derivative compatibility for the exact four-wave substitution. Extracting
the product of the four distinct wave variables kills every divergence
when the four momenta sum to zero. The
[actual scalar consumer](../../../Physics/FieldTheory/Jets/ScalarQuarticFourWitness.lean)
uses null momenta (1,0,0,1), (1,0,0,-1), (-1,-1,0,0), (-1,1,0,0). The full
free differential ideal maps to zero, and `four_value` gives value 48 on
K squared. Thus `quotient_nonzero` proves survival in the actual quotient.
This is a purely algebraic substitution, not an S-matrix equivalence.

The same file proves that this separator is not Lorentz invariant. On the
fourth power of the time first jet, its values before and after the real
unit shear are 24 and 60. This rejects this particular separator as a global
input coefficient; it is not a nonexistence theorem for invariant separators.

[ScalarQuarticContractions](../../../Physics/FieldTheory/Jets/ScalarQuarticContractions.lean)
defines the specified contractions

$$
A=\phi^2\sum_{i,j}\eta_i\eta_j(\partial_i\partial_j\phi)^2,
\qquad
B=\phi\sum_{i,j}\eta_i\eta_j
 (\partial_i\partial_j\phi)(\partial_i\phi)(\partial_j\phi),
\qquad C=K^2.
$$

Here eta=(1,-1,-1,-1). Explicit divergence currents and full differential
EOM membership prove q(A)=-2q(B)=q(C). The actual image of the span of these
three polynomials is therefore exactly the nonzero line generated by q(C),
with dimension 1. No multiplication closure of IBP is used. This proves
complete reduction for the stated candidate span, not coverage of the
entire invariant coefficient space.
`candidate_grade` places the whole candidate source in the actual (4,4)
grade, and `candidate_image_fixed` proves that every class in its image is
fixed by every actual Lorentz group element. This does not assume that the
raw candidate span covers all invariant coefficients or has an invariant
complement in the entire grade.

The [new coordinate diagnostic](../../../tools/derivative-literature/check-scalar-group.py)
uses the four actual group matrices above, rather than infinitesimal rows.
For derivative orders 0,2,4 it enumerates 1,20,305 monomials; the EOM/IBP
ranks are 0,11,235 and the combined ranks are 0,20,304. It constructs and
checks a normalized finite dual, with 48 nonzero entries at order 4. The
literal K squared vector is fixed by all four matrices and completes the
finite quotient. These are exact rational Python checks, not Lean premises.

At this topic's original stop, both planned routes left concrete obligations:

- Structural: prove that every admitted order-four invariant coefficient is
  determined by its value on K squared, beyond the three-contraction span,
  and construct a full-group invariant, globally relation-annihilating
  coefficient with normalized value 1. The constructed four-wave coefficient
  fails the explicit shear invariance equation above.
- Coordinates: identify the enumerated 305 coordinates and their rows with
  the entire actual selected source/full relation preimage inside Lean, then
  certify elimination and promote the finite dual's four transformation
  checks to invariance under arbitrary SL(2,C). The matrices are proved
  actual; these remaining source, relation and all-group claims are not.

That original stop was not a counterexample to the paper or a proof of
impossibility. The successor subsequently proved complete source coverage,
evaluation injectivity and a normalized 36-wave coefficient, invariant
under every actual Lorentz group element on the selected grade and
annihilating the full unbounded relation module. Its inverse/evaluation
laws give the complete dimension-1 coefficient theorem. No global invariant
extension to other grades is asserted or required. The original fixed-wave
separator remains a valid noninvariance control.

## Convention boundary

[1706.08520v1 Eq. (6.3)](https://arxiv.org/pdf/1706.08520v1), PDF pp. 58–59,
gives the four-scalar coefficients (1,0,1) at orders 0,2,4 and the K squared
representative at order 4. The native Lorentz order-0 and order-2 results
agree with those counts; the successor also completes the native order-4
coefficient line. Lean does not identify the complete Lorentz
coefficient space with the paper's SO(4)/O(4) Euclidean count. No Wick/group
equivalence, Hilbert-series identity or paper-wide basis is claimed.

The subsequent [existing and additional validation](validation.md) checks
these results through the common input operations and an additional normalized
scalar reference. It records the nonzero anisotropic order-two countercheck,
helper compatibility and independent polynomial evaluation. Those predecessor
checks did not close order-four completeness. The later
[complete-coefficient literature recheck](../scalar-quartic-four-completeness/literature-validation.md)
uses the proved successor equivalence and records the completed bounded
comparison, while preserving the Euclidean and whole-paper boundaries.
