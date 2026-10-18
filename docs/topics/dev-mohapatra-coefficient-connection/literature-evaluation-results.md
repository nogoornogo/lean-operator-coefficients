# Literature-Informed Coefficient Evaluation

The [fixed evaluation plan](literature-evaluation-plan.md) and subsequent
[all-degree re-evaluation](coefficient-reevaluation-plan.md) are complete.
The [Lean adapter](../../../Physics/StandardModel/Operators/DevMohapatraLiteratureConvention.lean)
derives the right-block matrix dictionary from the related sources, then uses
the exact tree elimination. The new
[all-degree comparison adapter](../../../Physics/StandardModel/Operators/DevMohapatraCoefficientReevaluation.lean)
composes this dictionary with the literal Hermitian action and its exact heavy
elimination. Adoption of the source normalization remains conditional.

## Matrix and kinetic dictionary

Dev et al., [1404.1003v4](https://arxiv.org/pdf/1404.1003v4), Eq.(3.31) and
Appendix B.1 Eqs.(B.1)–(B.5), specify C = i gamma0 gamma2 and Weyl gamma
blocks. With those blocks, gamma0 is the repository gamma4 and the Minkowski
gamma2 is -i times its Euclidean gamma2. The resulting C is **minus** the
repository C. The gamma2 gamma4 definition in the inspected
[Mohapatra–Senjanovic manuscript](https://inspirehep.net/files/78ee796b5ef38d1d83d344fd170b03f8),
Appendix A p.33, gives the same explicit C. Both equalities and both-sided
inverse identities are now Lean theorems, rather than inspection observations.

Right chirality uses the **lower** block in these dictionaries. The old paper
calls the upper block left; the repository's earlier right-block convention
uses the upper block. The new adapter embeds the two generators in the lower
block and proves that the literal inverse-C contraction is minus the epsilon
pair. It independently builds and transports the down current and six-quark
operator. Merely substituting the C matrix into the old upper-block convention
would give the wrong dictionary.

The related sources provide conventional kinetic normalization as a documented
candidate input. The old manuscript ties its chiral kinetic action and mass
half together in Eqs.(A.9)–(A.12). The existing conditional
`ChiralActionConvention.majorana_kinetic` proves that the four-component
Majorana kinetic half compensates the two conjugate blocks, up to its formal
total derivative. It introduces no vertex half or square-root-two by itself.
That theorem and its Pauli/time identities are included in the new strict audit.
Its differentiated odd components remain explicit inputs: this is not a
full kinetic calculus, IBP certificate, Wick rotation, or source-action match.

## Exact tree result

Adopt canonical fields and identify M with the target Majorana mass parameter.
Keep the target's positive M/2 inverse-C mass term; this maps to -M n0 n1.
Each inverse-C vertex maps its coupling to its negative. The target product
of three inverse-C bilinears maps to minus printedOperator. These choices
are translated consistently, including the mass; they are not extracted from
the old paper's C-bilinear mass sign by ignoring C versus C inverse.

For one N, the selected u,d,s channel, scalar quadratic parameter
m = plus or minus Mchi squared, and nonzero masses, the coefficient of the
literal lower-block inverse-C operator in the generated action is

```
C_tree = -(lambda * b)^2 / (2 * Mchi^4 * M_N).
```

The theorem `generated_literature` connects the generated polynomial to the
independently constructed literature operator. The new
`projectedAction_coefficient` connects the all-degree eliminated literal
Hermitian effective action directly to that same operator and coefficient.
For a nonzero real scalar quadratic parameter,
`DevMohapatraHeavyHermitian.holomorphic_full_action` supplies the original
scalar UV-action transport. Thus H.c. terms, heavy stationary substitution
and higher external-degree corrections have now been included exactly.
The holomorphic projection extracts the unbarred six-quark channel; it does
not assert that the entire eliminated action contains only this channel. Changing
the scalar quadratic mass sign leaves this coefficient unchanged; the scalar
is exchanged twice. The exact comparison with the positive scalar printed
in target Eq.(4) is:

| Selected flavor dictionary | Generated action coefficient | Ratio to literal printed scalar |
| --- | --- | --- |
| Independent d,s entry: b = z = lambda-prime_12 | -(lambda z)^2 / (2 Mchi^4 M_N) | -8 pi^2 |
| Both ordered antisymmetric entries, with no flavor half: b = 2z | -2 (lambda z)^2 / (Mchi^4 M_N) | -32 pi^2 |

Both ratios are Lean theorems; the second uses the proved factor-four coupling
rescaling and the earlier ordered-flavor identity. For nonzero couplings the
magnitude ratios are approximately 78.96 and 315.83. These decimal values
only describe dimensionless algebraic ratios, not rates or bounds.
A full ordered sum with a flavor half returns to the first row. The target's
actual sum convention is still not certified.

## Evaluation and limits

The literature-informed right-block dictionaries reproduce the earlier
magnitude discrepancy; they do **not** supply a 16 pi squared tree factor.
Conjugation phase, Majorana kinetic half, scalar mass sign, and the two
selected flavor-sum interpretations examined here do not remove it under
the adopted normalization. This gives stronger provenance to the conditional
comparison than an arbitrary undocumented choice.

The minus sign is the coefficient in the supplied action convention. A
Hamiltonian versus Lagrangian convention can reverse an overall sign; the
paper's operator label alone does not certify which signed comparison it
intends. No paper sign error is asserted. A nonzero invariant coefficient,
a generated polynomial in a supplied UV action, and a fully source-matched
physical coefficient remain distinct results.

## Updated assessment after all-degree elimination

The conditional mismatch survives exact elimination of the supplied full
Hermitian action. `independent_comparison` and `ordered_comparison` now state
the comparison as identities of projected action polynomials, rather than
only a comparison of separately supplied scalar prefactors. Neither the
conjugate sector nor omitted higher powers of the finite heavy kernel can
remove the discrepancy within this action and dictionary. The associated
[H.c. compatibility proof](heavy-elimination-results.md) also establishes that
stationary substitution preserves the anti-involution and the eliminated
full action is Hermitian.

| Question | Current status |
| --- | --- |
| Does exact H.c./all-degree elimination change the selected coefficient? | No; proved for the supplied derivative-free action |
| Can the examined scalar sign or flavor dictionaries supply the printed factor? | No; exact ratios remain -8 pi² and -32 pi² |
| Is the target's exact signed physical coefficient uniquely recovered? | No; source normalization and adoption remain conditional |
| Is a paper error certified? | No; the demonstrated discrepancy is conditional |

Eq.(4) of [the target's accepted version](https://arxiv.org/pdf/1504.07196v2)
prints the positive denominator `16 pi² Mchi⁴ MN` and H.c.; the preceding
text describes the graph as tree-level. These statements were rechecked
against the previously acquired PDF text. The all-degree proof supplies no
such pi factor under the adopted canonical dictionary. This identifies the
remaining issue more narrowly as a source matching/normalization question,
without selecting an undocumented interpretation of the paper.

Remaining inputs: actual adoption of the related spinor/kinetic dictionary,
canonical scalar normalization, identification of printed couplings with the
selected component vertices, the target's flavor summation and signed
Lagrangian/Hamiltonian convention, and physical interpretation of the
concrete Grassmann carrier. The literal H.c. dictionary and full stationary
elimination are now proved and are no longer missing algebraic steps.
No loops, rates, additional N or flavors, or author contact are included.
The result is a stronger **conditional** coefficient evaluation, not a
complete paper-error certificate.

## Nonzero action and required normalization

The subsequent [closure result](normalization-closure-results.md) proves
nonzero of the concrete literature operator and the actual action inequalities
for both flavor dictionaries. It also proves the matching iff
`-8 pi² (a b)² = t mu² nu` for explicitly parameterized component/source
identifications. A consistent common bilinear convention change cannot
remove the mismatch. Source adoption remains unproved.

## Review closure on magnitudes

The [review-closure result](review-closure-results.md) proves that arbitrary
unit phases, including either global sign, cannot supply matching magnitude
in the multiplier family. It also proves action inequality under an explicit
bounded compensation condition. Universal rational/algebraic multiplier
exclusion was deferred because the needed pi-squared irrationality or pi
transcendence theorem was not found in the pinned library. The review's
phenomenological estimates and paper-error assertion are not adopted.
