# Literature Recheck With Complete Scalar Coefficients

All three entries in the [comparison contract](literature-validation-plan.md)
reach their bounded endpoints. No disagreement is found in the stated native
scalar comparisons. The new checks use the entire selected coefficient
space, including existence and uniqueness, rather than only a nonzero class
or the three named contractions.

## Sources and convention dictionary

The pinned primary PDF text was reinspected; no visual PDF inspection is
claimed. These sources guide comparisons and supply no Lean premise.

| Source and inspected location | Comparison |
| --- | --- |
| Henning et al., [1706.08520v1](https://arxiv.org/pdf/1706.08520v1), Section 6.1, Eq. (6.3), PDF p. 58; representatives on p. 59 | Four identical scalar fields: coefficients (1,0,1) at derivative orders 0,2,4, with K squared representing order four. |
| Cao et al., [2105.12742v3](https://arxiv.org/pdf/2105.12742v3), Section 3.1, PDF pp. 13–15; Eqs. (3.28)–(3.29), PDF p. 20; Eq. (A.20), PDF p. 43 | Three normalized densities, their chosen combination, and one physical four-field/four-derivative operator. The momentum variables are dot products without a factor of two; permutation sums retain distinct terms. |
| Lehman–Martin, [1510.00372v1](https://arxiv.org/pdf/1510.00372v1), Eq. (2.8), PDF p. 9 and discussion on p. 10 | Two-derivative scalar redundancy; the single-scalar four-derivative example is also counted correctly. The displayed subtraction failure starts at six derivatives. |

The native input is one commuting scalar generator over the complex numbers,
with ordinary symmetric jets, actual SL(2,C) Lorentz action and metric
(+---). This is the complexified coefficient problem for one real scalar,
not two independent charged scalar species. The free equation is the wave
equation. Its entire differential ideal and the linear range of total
divergences enter the selected relation preimage. IBP is not ideal-closed.

Write K for the metric contraction of two first derivatives, C=K squared,
A for phi squared times the contracted Hessian squared, and B for phi times
the Hessian contracted with two gradients. The explicit density dictionary is:

| Paper density | Native density | Quotient class | Normalized coefficient value |
| --- | --- | --- | ---: |
| o1 | A/4 | q(C)/4 | 1/4 |
| o2 | B/2 | -q(C)/4 | -1/4 |
| o3 | C/8 | q(C)/8 | 1/8 |
| o1 - 2 o2 + 6 o3 | chosen | (3/2)q(C) | 3/2 |

These are local polynomial normalizations. The independent diagnostic also
checks the literal permutation polynomials with 6,12,3 distinct terms. No
physical amplitude normalization or general operator/amplitude equivalence
is inferred from those finite evaluations.

## Complete selected-input checks

The persistent [Lean consumers](../../../Physics/FieldTheory/Jets/ScalarQuarticLiteratureChecks.lean)
prove:

- `bounded_counts`: the complete order-zero actual image has dimension 1,
  the entire order-two invariant coefficient space has dimension 0, and
  the entire order-four invariant coefficient space has dimension 1.
  The zero-order entry is an image theorem, not an assertion that all three
  entries have the same type. K-squared evaluation supplies the order-four
  equivalence and normalized inverse from the completed theorem.
- `first_value`, `second_value`, `third_value`, `chosen_value`: every
  selected coefficient has paper-density values proportional to
  (1/4,-1/4,1/8,3/2), with its K-squared value as the common coordinate.
- `chosenEquivalence`: evaluation on the paper's chosen combination is a
  linear equivalence. A requested value z uniquely gives coefficient
  (2z/3) times `normalized`; `chosen_reconstruction` proves the inverse on
  every admitted input.
- `admitted_triple`: prescribed density values (a,b,c) are realized by a
  unique admitted selected coefficient if and only if b=-a and a=2c.
  The coefficient is 8c times `normalized`. In particular the values
  (1,0,0) are rejected, so the three densities are not independent after
  the specified EOM/IBP relations.

## Per-source endpoints

C2's bounded counts and order-four representative agree with the complete
native Lorentz result. The previous missing native coefficient-completeness
step is closed. A formal equivalence with the paper's Euclidean SO(4)/O(4)
coefficient spaces and the arbitrary-derivative Hilbert series remain open.

For Cao, the density normalization and unique native coefficient coordinate
agree with the one-operator count in this sector. Evaluation on the chosen
combination now determines all selected coefficients. Annihilation by the
special conformal generator, the off-shell/form-factor basis, dimensional
regularization and renormalization results are not checked.

For Lehman–Martin, the entire native four-field order-two coefficient space
vanishes and the order-four space has dimension one. This is consistent
with the low-order scalar examples. The six-derivative failure example and
the general subtraction rule or SMEFT tables are not verified here. The
queue continues to this endpoint despite the preceding sources' remaining
group/conformal boundaries.

The old anisotropic controls remain: a nonzero un-invariant quotient class
need not support a nonzero invariant coefficient, and the full order-four
quotient is larger than the K-squared candidate line. No invariant extension
of a selected coefficient to all grades is asserted. Commands, strict
inventories, diagnostics and repository gates are in the
[verification record](verification.md#literature-validation-gate).
