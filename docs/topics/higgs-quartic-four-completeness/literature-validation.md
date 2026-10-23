# C4 existing and new literature validation

The three primary displays in [references](references.md) have been inspected
directly, including the PDF tables and formulas. The formal consumers are
[HiggsQuarticFourLiterature](../../../Physics/FieldTheory/Jets/HiggsQuarticFourLiterature.lean).
The final aggregate, strict audit and independent queue gates pass in
[verification](verification.md). All three comparisons agree within the
stated specialization; each receives its own result below.

## Frozen dictionaries

All comparisons use the free, gaugeless ordinary-derivative specialization
and the stated complex field/dual dictionary. Numbering below is one based.

| Primary source | Native density values in q coordinates | Formal comparison |
| --- | --- | --- |
| Murphy, 2005.00059v6, Section 4.1, Table 2, PDF p. 20 (printed p. 19) | (q1,q2,q3) | `murphyEquivalence` evaluates all admitted whole-grade coefficients, with the complete inverse and dimension inherited from the public theorem. |
| Li et al., 2005.00008v3, Section 4.2, Eq. (4.8), PDF p. 31 | (4q3,q1,q2-q1-q3) | Literal higher-derivative densities have grade (4,4). Full free EOM and linear IBP prove their values for every relation-annihilating linear functional. The invertible coordinate map supplies `liEquivalence` on the actual selected input. |
| Eboli–Gonzalez-Garcia, 1604.03555v1, Section III.A, Eq. (16), PDF p. 5 | (q2,q3,q1) for (O_S,0,O_S,1,O_S,2) | `eboliEquivalence` is the permutation of the complete coefficient input. `omitted_S2` constructs a nonzero admitted coefficient invisible to the first two densities. |

Li's inverse map from native values (l1,l2,l3) is
(l2,l3+l2+l1/4,l1/4). The factor four is a consequence of the written
density rho Box squared rho and the free equations, not a fitted
normalization. The proof uses Box self-adjointness modulo linear IBP,
the free Box rho identity, Hessian-product reduction and the current's
Box-product rule. It does not assert a literal off-shell equality of the
three density lists.

Eboli's footnote 2 explicitly includes O_S,2 relative to its cited earlier
conventions. This check uses the displayed three-density list; it does not
judge an unexamined older list or certify the subsequent gauge-boson
coupling formulas.

## Independent queue and negative controls

The standard-library [per-paper queue](../../../tools/derivative-literature/check-higgs-literature.py)
reads each dictionary independently on four rational null/conserving
configurations and four color-amplitude assignments. It records a local
discrepancy and continues to the next paper. Its continuation control
deliberately changes Li's factor four to three: that comparison must fail
while Eboli is still checked. The actual dictionaries are retained unchanged.

All three actual paper checks pass 16 configurations/amplitude assignments
each, with tested rank three. The intentionally incorrect Li factor is
detected, and the following Eboli comparison still passes. Thus local
comparison failure does not terminate the queue.

The separate [colored-wave diagnostic](../../../tools/derivative-literature/check-higgs-four.py)
checks explicit quotient values, divergence rows, simultaneous wave
permutations and an internal shear. Removing conservation gives a nonzero
divergence, and removing nullness gives a nonzero EOM product. Omitting a
candidate reduces the tested rank. These are independent exact diagnostics,
not Lean premises. The old raw probe's IBP failure remains a proved control.

## Limits

Agreement here concerns these native densities and their complete algebraic
coefficient space in the selected specialization. Covariant-derivative
commutators, gauge-field sectors, interacting/Yukawa EOM, real Hermitian
coordinates, full SMEFT counts, scattering, running and phenomenological
bounds remain outside the comparison. A paper-specific discrepancy or
missing bridge never supplies a premise or prevents the remaining queue
from being processed.
