# Dev–Mohapatra: Conditional Six-Quark Coefficient Evaluation

This study evaluates the selected u,d,s channel of one heavy Majorana N in
[arXiv:1504.07196v2](https://arxiv.org/abs/1504.07196v2), Eqs.(1),(3),(4).
Eq.(4) displays a denominator `16 pi² Mchi⁴ MN`; the accompanying text calls
the route tree-level. [Source locations and inspection hashes](../../topics/dev-mohapatra-coefficient-connection/references.md)
record the PDF, TeX and accepted-manuscript checks.

## What is proved

For the explicit supplied derivative-free action, scalar elimination and
heavy-fermion elimination are exact, including H.c. and all external degrees
on the finite Grassmann carrier. The proof derives actual left stationary
equations, a unique solution, an exact finite kernel inverse, and substitution
preserving Hermitian conjugation. The unbarred projection recovers the
selected six-quark channel, without assuming barred-heavy fields vanish.
See the [all-degree result](../../topics/dev-mohapatra-coefficient-connection/heavy-elimination-results.md).

The related-source C matrices and lower/right block are transported
consistently through the mass, vertices and three-bilinear operator. Under
the adopted canonical dictionary, the coefficient is

```
C_tree = -(lambda*b)^2 / (2 Mchi⁴ MN).
```

| Selected flavor interpretation | Ratio to the literal Eq.(4) scalar |
| --- | --- |
| Independent entry b=z | -8 pi² |
| Both ordered antisymmetric entries, no half: b=2z | -32 pi² |
| Ordered sum with a half | First row |

These are identities of the projected all-degree action. The concrete
literature operator on eighteen independent components is proved nonzero;
with nonzero masses and couplings, the supplied action differs from the
literal Eq.(4) action. These inequalities concern the selected channel,
not absence of other terms in the full effective action.
See the [evaluation](../../topics/dev-mohapatra-coefficient-connection/literature-evaluation-results.md)
and [nonzero-action result](../../topics/dev-mohapatra-coefficient-connection/normalization-closure-results.md).

## Normalization and phases

If the component scalar quadratic parameter, Majorana mass and vertices
are mu*m, nu*M, a*lambda and b*z, and the comparison operator is t*O,
matching is equivalent to

```
-8 pi² (a b)² = t mu² nu.
```

The theorem requires nonzero original masses/couplings and nonzero mu,nu;
invertible dictionaries additionally require nonzero a,b,t. These are
independent source/component identifications, not automatically consistent
field redefinitions. A consistent common bilinear change cannot remove
the discrepancy.

Taking norms proves that arbitrary unit-modulus multipliers, including
either global sign, cannot match. More generally, matching is impossible
for nonzero a,b if `|t| |mu|² |nu| <= 32 (|a| |b|)²`. This is a sufficient
bounded condition, not an exhaustive classification of normalizations.
See the [magnitude obstruction](../../topics/dev-mohapatra-coefficient-connection/review-closure-results.md).
Universal rational/algebraic exclusion remains deferred; pi irrationality
alone is insufficient to establish pi-squared irrationality.

## What remains conditional

Original Hermitian scalar UV-action transport requires a real nonzero
scalar quadratic parameter. The target's adoption of the related spinor/
kinetic dictionary, canonical scalar normalization, printed-to-component
coupling identification, exact flavor sum and Lagrangian/Hamiltonian sign
remain unproved. The literal supplied H.c. dictionary and all-degree heavy
elimination are proved and are no longer missing steps.

The mismatch is therefore a conditional action result, not a certified
paper error or a unique corrected physical coefficient. No amplitudes,
QCD dressing, rates, bounds, loops, additional N/flavors or baryogenesis
consequences are derived. The user-supplied external review reports source
inspection but no independent Lean rebuild; its downstream estimates are
not adopted.

## Verification

The [topic ledger](../../topics/dev-mohapatra-coefficient-connection/verification.md)
records focused builds, persistent strict transitive axiom audits and the
full 6741-job build for the latest proof phase. Only propext, Classical.choice
and Quot.sound are permitted in the new strict audits. Bounded scripts
supplement these proofs and are not proof premises. The
[topic overview](../../topics/dev-mohapatra-coefficient-connection/README.md)
retains plans, phase records and integration verification.
