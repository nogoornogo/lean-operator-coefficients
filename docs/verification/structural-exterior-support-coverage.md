# Structural Exterior Support Coverage

| Source and location | Comparison target | Verified interpretation | Conditions and limits | Evidence |
| --- | --- | --- | --- | --- |
| Christian Pauly, [Strange duality revisited](https://math.univ-cotedazur.fr/u/pauly/SDR.pdf), §3.2, equation (4), PDF p.6; citing Procesi, Chapter 9, Theorem 8.4.1 | `TopExteriorCauchy`, `ExtremeCauchyBlocks`, `SU2ExteriorBlocks` | Explicit top-column Cauchy map into an exterior tensor power, naturality, determinant covariance, nonzero evaluation and the injectivity needed for the Q/L blocks | The cited Cauchy decomposition guides the construction; no decomposition theorem is imported as a premise. Determinant-one actions and the applicable irreducibility facts are explicit/proved. The whole Schur decomposition, affine theory and complete SM support iff are not claimed. | [Assessment](../topics/sm-computable-characters/support-structure-assessment.md), [result](../topics/sm-computable-characters/structural-results.md), [verification](../topics/sm-computable-characters/structural-verification.md) |
| Niven Achenjang, notes for Pavel Etingof's [18.755 Lie Groups and Lie Algebras II](https://people.math.harvard.edu/~achenjang/assets/pdf/18_755_Notes.pdf), Theorem 5.4, printed p.27 | `SymmetricCauchy`, `ExtremeCauchyBlocks` | The row component `Symⁿ B ⊗ Symⁿ C → Symⁿ(B ⊗ C)`, its pure-power evaluation and naturality; composite injectivity for independently acting SU(2) symmetric powers | Separate finite symmetrization is proved using pinned polarization/symmetric-power APIs. General Schur branching and arbitrary mixed-species Kronecker positivity are not supplied by this result. | Same structural result and verification above |

The accompanying complementary-degree duality, balanced weak-weight bound,
independent-generation injections and CG constituent witnesses are proved
mathematical adapters. Actual coefficient vanishing above the sharp bound is
already connected; a subrepresentation witness alone is not reported as a
completed invariant-coefficient classification. No new external mathematical
premise, dependency or toolchain change is introduced.

For the Q18 middle degree, the proved determinant-one wedge pairing now
connects the Cauchy constituent to an actual nonzero local coefficient/kernel
without a new literature input. Charge restoration is proved, and the result
is uniform over even m <= 18 at delta -6 with trivial residual action.
See [Q18 results](../topics/sm-computable-characters/q18-support-results.md) and
[verification](../topics/sm-computable-characters/q18-support-verification.md).
The exact numerical predecessor is archived; this checkpoint did not yet
establish the full Q/L support iff supplied by the later consumers below.

The later [non-numerical consumers](../topics/sm-computable-characters/non-numerical-support-results.md)
connect all six lower-half constituent families to actual local coefficients
and kernels using proved compact Hom support symmetry and weak self-duality.
They classify original-Higgs support for all constant positive L degrees and
Q degrees through 18, retaining the existing scalar cyclic q/l action.
Parity, capacity and exact hypercharge/residual conditions are proved in both
directions; no Weyl torus-reduction premise or computed multiplicity is used.
This bounded consumer does not complete upper-half Q, signed conjugates,
arbitrary mixed contents or the 572-assignment search. See its
[verification](../topics/sm-computable-characters/non-numerical-support-verification.md).

The [signed/mixed continuation](../topics/sm-computable-characters/signed-mixed-results.md)
uses complementary duality to close Q24 and the all-degree original-Higgs
criterion for both Q signs, with both L signs also closed. Individual admissible
Q/L constituent tests now have explicit degree/charge predicates. Arbitrary
mixed conjugation and independent-chirality exclusions are proved, and eight
selected mixed four-fermion families have exact original-field support iff.
No new literature premise is used. The full mixed branching interface remains
at its [recorded gate](../topics/sm-computable-characters/signed-mixed-stop.md);
these consumers are not arbitrary mixed-content completeness or a full
assignment search. See [verification](../topics/sm-computable-characters/signed-mixed-verification.md).

The [joint components](../topics/sm-computable-characters/joint-branching-results.md)
retain color/hypercharge while decomposing weak and independent-spin labels;
their general algebraic occurrence criterion remains Weyl-conditioned.
The [structural mixed consumers](../topics/sm-computable-characters/structural-classification-results.md)
add actual complementary weak/overflow exclusions and a complete empty/full
mixed-family iff with no Weyl or numerical premise. These use proved compact
line triviality and actual charge actions rather than assuming general Schur
branching. General partially occupied mixed classification remains open at
the [positive-branching interface](../topics/sm-computable-characters/structural-classification-boundary.md).
The additional Manivel/Ikenmeyer--Panova special-case positivity theorems are
research candidates only, not adopted premises or claimed Lean coverage.
See the [structural verification](../topics/sm-computable-characters/structural-classification-verification.md).
