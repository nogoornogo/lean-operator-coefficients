# Existing And Additional Scalar Verification

The [verification contract](validation-plan.md) is executed on the existing
topic branch. All stated Lean consumers and exact diagnostics pass. No
disagreement is found in these scopes. The original C2 order-four invariant
completeness boundary is unchanged; this verification does not close it.

## Actual input consumers

| Check | Result | Evidence and limit |
| --- | --- | --- |
| C1 restriction and inverse | Every normalized global coefficient with value c restricts to the inverse coordinate c in each of the three completed sectors. | [Math consumers](../../../Math/RepresentationTheory/ScalarCompletenessChecks.lean), `first_restriction`, `second_restriction`. |
| C1 quotient extraction | The selected-input coefficient map and selected-to-actual-image equivalence return the explicit first-jet coordinates on arbitrary selected polynomials. | `first_selected_evaluation`, `second_selected_evaluation`, `first_image_evaluation`, `second_image_evaluation`. |
| C1 presentation and exchange | Values survive arbitrary transported linear presentations. Species exchange changes the chosen (1,1) first-order coordinate by -1 and fixes the (2,2) second-order representative. | `first_transported`, `second_transported`, `first_swap_sign`, `second_swap_value`; the transported action and relations are retained. |
| IBP product control | q(phi')=0 but q(chi phi') is nonzero. | `ibp_product_control`; the full EOM/IBP relation module is not being ideal-closed. |
| C2 complete order-two coefficient test | Every global admitted coefficient restricts to zero on the entire grade, including coefficients supplied by the helper input. | [Physics consumers](../../../Physics/FieldTheory/Jets/ScalarCompletenessChecks.lean), `Two.global_zero`, `Two.helper_zero`. |
| C2 anisotropic countercheck | p=phi squared times the time first jet squared is in grade (4,2); its actual quotient class is nonzero, but no global invariant coefficient can have value 1 there. | `Two.anisotropic_grade`, `Two.anisotropic_nonzero`, `Two.anisotropic_coefficient_rejected`. The full-group coefficient space is zero; the full un-invariant quotient is not. |
| C2 helper and contraction compatibility | K squared survives in the helper-generated free quotient. Every admitted direct/helper coefficient satisfies f(A)=f(C), f(B)=-f(C)/2. | `Four.helper_nonzero`, `Four.coefficient_A`, `Four.coefficient_B`, `Four.helper_coefficients`; no invariant extension is presumed. |

The anisotropic class is separated by value -8 under the full-relation
four-wave functional. That functional is not Lorentz invariant, consistently
with the existing 24/60 shear counterexample. Thus the vanishing theorem
does not accidentally assert that the whole order-two quotient is zero.

The existing derivative/nonderivative, presentation, reality, generated-input
and six-case comparison audits are also re-elaborated. Their unchanged Higgs,
Weyl and nonderivative scopes remain those of the predecessor portfolio.
Successful regression does not promote their partial literature comparisons
to complete bases.

## Literature queue

All four entries were processed to their local endpoint; a partial endpoint
did not end the queue. Version pins and source roles are in
[references](references.md).

| Source | Checked comparison | Endpoint |
| --- | --- | --- |
| Existing C1, 1507.07240v1 Eq. (3.11) | The specified contents at orders 0,1,2 give (1,1,0)/(1,1,1); new coefficient restriction and normalization checks pass. | Complete bounded sectors; no full-series theorem. |
| Existing C2, 1706.08520v1 Eq. (6.3) | Order-two full-group coefficient vanishing and the nonzero order-four K squared class are retained; helper and fixed-candidate relations pass. | Partial at order four; full invariant spanning/dual and Euclidean group bridge remain open. |
| Existing survey, new concrete comparison: Lehman–Martin 1510.00372v1 Eq. (2.8), PDF p. 9 | Its single-scalar two-derivative redundancy is checked at four fields through the whole actual Lorentz grade, not only the named contraction. | Native free scalar statement proved; higher-derivative subtraction and SMEFT tables are not certified. |
| New source: Cao et al. 2105.12742v3 Eqs. (3.28)–(3.29), PDF p. 20 | The written density normalizations are read as o1=A/4, o2=B/2, o3=C/8 in the native Lorentz algebra. Their combination has quotient value (3/2)q(C). | Algebraic normalization and nonzero class proved; conformal-primary annihilation, full physical basis and renormalization are not certified. |

For the last entry, `Cao.quotient_normalization`, `Cao.nonzero`,
`Cao.separator_value` and `Cao.coefficient_value` prove the precise local
contract: q(o1-2o2+6o3)=(3/2)q(C), its class is nonzero, the fixed-wave value
is 72, and every admitted coefficient obeys the same value relation. These
are consequences of the actual free EOM/IBP relations, not an imported paper
count or conformal representation premise.

## Independent polynomial cross-check

[check-scalar-waves.py](../../../tools/derivative-literature/check-scalar-waves.py)
imports no finite-rank implementation. It directly expands the jet
substitution and ordinary derivative products using exact rational arithmetic.
Ordered derivative allocations followed by commuting-factor deduplication
independently recover source sizes 1,4,20,80,305 at four fields and orders
0 through 4.

- Six rational null, momentum-conserving configurations pass 2520 divergence
  checks and 330 differential-equation product checks. These exhaust four-field
  divergence precursors of derivative order at most 3 and wave descendants
  times three-field multipliers through total derivative order 4, per case.
- All configurations satisfy A=C=-2B. K squared values are 48, 1456/25,
  10416/169, 64, 64, 48. All 144 wave-label permutation and 12 common
  nonzero momentum-rescaling checks preserve the expected value/scaling.
- The three normalized densities are compared to literal distinct-term
  permutation polynomials in eight configurations, including the two
  assumption-removal controls. The dot-product variables have no factor of
  two; they are not the usual doubled Mandelstam variables. At the original
  momenta the values are (12,-12,6), and the stated combination gives 72.
- Null momenta without conservation give divergence value -48. Conserving
  nonnull momenta give a free-equation product value 12. The fixed-wave
  invariance control returns 24 before and 60 after the actual real shear.

These negative controls succeed by detecting the removed condition. They
are not failures of the stated theorem. The finite checks are reproducible
diagnostics, not global proofs or new premises. The retained three exact
rank/count scripts also pass without changed expectations.

## Remaining boundary

No proof was weakened and no original public input or dependency pin changed.
No contradiction or regression is found within the proved and exactly tested
domains. The fixed-wave separator and the normalized candidate combination
do not establish an invariant global separating coefficient or complete
order-four invariant spanning. No analytic amplitude, all-order field
redefinition, interacting graded-basis or Euclidean/Lorentz equivalence is
inferred. Commands and acceptance evidence are owned by the
[verification record](verification.md#additional-validation-gate).
