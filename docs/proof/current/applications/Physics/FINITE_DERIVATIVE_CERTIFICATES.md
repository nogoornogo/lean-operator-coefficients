# Actual Finite Derivative Certificates

The [certificate](../../../../../Math/RepresentationTheory/Jets/FiniteDerivativeCertificate.lean)
uses a finite complex source basis, a proved span equality for the actual
relations, and invariance constraints for the full input group. Its
`Presentation.equivalence` has both inverse laws; `reconstruction` identifies
actual source evaluation. An elimination matrix or Lie row family alone
does not construct these obligations.

The [quadratic control](../../../../../Math/RepresentationTheory/Jets/FiniteDerivativeScalarControl.lean)
constructs that presentation on the complete one-direction two-field,
two-derivative source. The off-shell row is (1,1); on shell all coordinates
vanish. The finite test is tied to the untruncated source and full relations.

For the actual massless Lorentz scalar in four directions,
[constant-jet projection](../../../../../Math/RepresentationTheory/Jets/JetConstantProjection.lean)
and its [consumer](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/ScalarConstantCoefficients.lean)
provide global invariant coefficients killing the whole free differential
EOM ideal and every divergence. The n-th coefficient detects phi^n with
value 1. The [source certificate](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/ScalarZeroDerivativeCertificate.lean)
reconstructs the entire derivative-degree-zero grade and gives a linear
equivalence of its image in the full EOM/IBP quotient with the complex
numbers. This holds for every field degree, including the C2 four-field case.

For the interacting seed Box phi + lambda phi cubed, existence of a global
coefficient with prescribed cubic value c is equivalent to lambda*c=0.
Necessity reuses the earlier relation; sufficiency uses the constructed free
coefficient when lambda=0, and zero otherwise. This is a target-specific
necessary and sufficient condition, not an interacting coefficient basis.

The [original topic record](../../../../topics/derivative-literature-foundations/finite-certificates.md)
retains its two attempted routes and original C2/C4 stops. Subsequent proved
positive-degree sectors are described below. No invariant-extension premise,
Hilbert-series theorem or paper-wide completeness result is introduced.

The [additional checks](../../../../topics/derivative-literature-foundations/extended-checks.md)
add complete actual C1 two-species zero-derivative images for every content,
and image dimension 0 for the entire (1,1), d=2 source. These use full
unbounded EOM/IBP relations, global separation at d=0 and exhaustive monomial
classification at d=2. The exact diagnostics also check surviving representatives
as well as ranks; this strengthens finite evidence without importing a
semantic/group bridge into Lean. The same follow-up identifies the entire
free scalar d=0 Hermitian image as a real one-dimensional subspace.

The [finite completeness follow-up](../../../../topics/scalar-derivative-completeness/results.md)
closes the remaining C1 contents (1,1),d=1 and (2,2),d=1,2. A four-variable
first-jet projection commutes with derivatives and kills the whole free
differential ideal; explicit global functionals also annihilate every IBP
relation. Complete monomial reconstruction, actual-image and coefficient
equivalences, both inverse laws and arbitrary normalized global values prove
dimension 1 in each sector. Thus the bounded C1 lists are (1,1,0)/(1,1,1).

For the complete actual four-field/two-derivative Lorentz grade,
[ScalarQuarticTwoCompleteness](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/ScalarQuarticTwoCompleteness.lean)
proves every admitted coefficient vanishes. Two actual sign flips and two
actual shears bound invariant bilinear forms; the trace relation and Leibniz
IBP kill all monomials. The ordinary linear extension in this proof is
assumed neither invariant nor relation preserving outside the selected grade.

At four derivatives, an exact four-wave substitution kills the full free
EOM/IBP module and evaluates K squared to 48. Hence its actual quotient class
is nonzero. The specified contractions A=phi squared times Hessian squared,
B=phi times Hessian times two gradients and C=K squared obey q(A)=-2q(B)=q(C);
their candidate span has actual quotient-image dimension 1. The fixed-wave
separator is provably not Lorentz invariant. The
[order-four successor](../../../../topics/scalar-quartic-four-completeness/results.md)
proves evaluation on K squared is a linear equivalence from the entire
selected admitted invariant coefficient space to the complex numbers, with
inverse c mapped to c times the explicit normalized coefficient. Complete
weighted source coverage and pair-symmetric rank-four controls supply the
upper bound. A normalized sum of 36 null, conserving wave functionals kills
the full relation module. Lean-checked moment identities and the actual
inverse Minkowski pairing prove its invariance on the whole grade.

The [input guide](../../../../topics/scalar-quartic-four-completeness/input-guide.md)
and [consumers](../../../../../Physics/FieldTheory/Jets/Scalar/QuarticFour/ScalarQuarticFourChecks.lean)
give direct/quotient extraction, whole-source restriction and normalized
A/B/C/Cao values. The time-gradient fourth-power probe has value 1/8 under
this coefficient, but its class lies outside the candidate image. The
un-invariant quotient is therefore larger than that line. The normalized
coefficient is on the selected grade; neither a global invariant extension
to all degrees nor a paper Euclidean/Lorentz convention bridge is assumed.

The [consumer verification](../../../../topics/scalar-derivative-completeness/validation.md)
tests restriction, quotient extraction, coordinate inverses, species exchange
and transported presentations. It also proves an anisotropic order-two class
is nonzero although every admitted Lorentz coefficient vanishes there. Thus
the zero coefficient result does not assert a zero un-invariant quotient.
Helper inputs preserve K squared survival and the stated contraction value
relations. The original normalized scalar density comparison gives a nonzero
combination equal to (3/2)K squared in the actual quotient. The successor's
[literature consumers](../../../../../Physics/FieldTheory/Jets/Scalar/Inputs/ScalarQuarticLiteratureChecks.lean)
prove evaluation on that combination is an equivalence on the entire
selected invariant coefficient space. The three paper-density values
(a,b,c) are admitted uniquely exactly when b=-a and a=2c. This is an
algebraic input certificate, with the dictionary and per-source boundaries
in the [recheck](../../../../topics/scalar-quartic-four-completeness/literature-validation.md);
no conformal-primary theorem or global invariant extension is supplied.

## Whole-grade Higgs coefficients

The [C4 result](../../../../topics/higgs-quartic-four-completeness/results.md)
proves evaluation on q1,q2,q3 is a complex linear equivalence for all
admitted invariant coefficients on the entire free Higgs grade (4,4),
under the actual global covering-SM and Lorentz action. Complete colored
source coverage, actual gauge constraints, EOM traces and explicit linear
IBP prove injectivity. Ordered null/conserving waves with kernel-checked
moments and invariant internal pairings construct a normalized inverse.
Both inverse laws, dimension 3 and direct/generated agreement are proved;
no caller moment, count, candidate-span or invariant-extension premise is used.

The [input guide](../../../../topics/higgs-quartic-four-completeness/input-guide.md)
and [literature consumers](../../../../../Physics/FieldTheory/Jets/Higgs/QuarticFour/HiggsQuarticFourLiterature.lean)
connect all selected coefficients to Murphy's contractions, Li's native
higher-derivative densities and Eboli's ordering. The [three-source validation](../../../../topics/higgs-quartic-four-completeness/literature-validation.md)
retains their distinct free/gaugeless dictionaries. The un-invariant
quotient, local gauge connections, interacting/Yukawa EOM, Hermitian real
coordinates and full SMEFT classification remain outside this coefficient
result. Individual old wave decoders are not presumed invariant, and the
raw probe's IBP rejection remains a control.
