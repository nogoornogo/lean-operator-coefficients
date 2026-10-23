# Progress And Results

## Complete upper control

[ScalarQuarticFourUpper.evaluate_injective](../../../Physics/FieldTheory/Jets/ScalarQuarticFourUpper.lean)
proves that evaluation on K squared is injective on the entire selected
admitted coefficient space. Thus there is at most one independent invariant
coefficient, without a candidate-span or invariant-extension premise.

The proof covers every weighted monomial through its four jet factors and
all 35 derivative allocations. Pair symmetry and actual sign flips/shears
reduce invariant rank-four tensors to two metric coordinates. EOM traces
kill the 4 and 3+1 partitions; the proved A=C=-2B relations and the fully
symmetric 1+1+1+1 tensor control kill the others when the K-squared value is
zero. The selected-input argument extends a linear map only for notation on
the grade, never as an invariant map on the full source.

The sparse row and source-coverage generators are retained under
`tools/derivative-literature/`. Their output is theorem source: every identity,
including elimination and exhaustive source coverage, is rechecked by Lean.
The square-free four-wave polarization identity is also proved algebraically.

## Normalized coefficient and complete equivalence

[ScalarQuarticFourCompleteness](../../../Physics/FieldTheory/Jets/ScalarQuarticFourCompleteness.lean)
constructs `normalized : selected.Coefficient` with value 1 on K squared.
Its `equivalence` maps every admitted coefficient F to F(K squared), with
inverse c mapped to c times `normalized`. Both inverse laws, extraction,
arbitrary values, nonzero support and coefficient dimension 1 are proved.
This closes the planned endpoint on the entire actual selected grade.

The raw functional is the sum of 36 exact null, conserving four-wave
functionals with common weight 1/27648. Each summand kills the whole free
differential EOM ideal and every linear divergence, at unbounded jet order.
The displayed Gaussian-integer data and all 1280 rank-four moments are
checked inside Lean by kernel reduction. No generated rank or external
integer table is an unchecked premise.

For the five derivative partitions, the normalized polarized moments have
the form a times the first metric pairing plus b times the other two:

| Partition | a | b |
| --- | ---: | ---: |
| 4 | 0 | 0 |
| 3+1 | 0 | 0 |
| 2+2 | -1/36 | 1/18 |
| 2+1+1 | 1/72 | -1/36 |
| 1+1+1+1 | 1/24 | 1/24 |

The inverse Minkowski pairing is proved invariant for every actual SL(2,C)
direction action, by polarization and the matrix inverse identities.
Multilinearity and complete source coverage then prove invariance on the
whole grade. The construction uses neither integration over a group nor a
semisimplicity or selected-coefficient-extension premise.

## Interface and scope controls

[ScalarQuarticFourChecks](../../../Physics/FieldTheory/Jets/ScalarQuarticFourChecks.lean)
checks the existing whole-source restriction and selected quotient extraction.
The normalized values are A=1, B=-1/2 and the Cao combination=3/2. The
anisotropic probe (time first derivative of phi) to the fourth power has
value 1/8, including after any actual Lorentz action.

That probe's quotient class lies outside the three-candidate image. The
proof compares the new invariant coefficient with the predecessor's fixed
wave separator, which gives 24 on the probe and 48 on K squared. Thus
coefficient dimension one does not identify the entire un-invariant quotient
with the K-squared line.

The endpoint fixes one commuting scalar, complex coefficients, free equation,
four fields and four ordinary derivatives in signature (+---). The normalized
input is selected on this grade; no global invariant extension to every
degree, interacting graded equivalence, arbitrary-degree Hilbert series,
Euclidean group bridge, conformal-primary or quantum result is claimed.
Public input definitions, dependency pins and the root README are unchanged.

The [literature recheck](literature-validation.md) uses this equivalence on
the paper-normalized density inputs. Evaluation on the Cao combination is
also an equivalence on the entire selected coefficient space. The three
prescribed density values have a necessary and sufficient compatibility
condition and a unique admitted coefficient. All three source comparisons
reach their bounded endpoints; Euclidean and conformal boundaries remain.
