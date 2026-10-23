# General theorems

These are algebraic results for supplied field representations and symmetry
actions. The general mixed coefficient theorem is derivative-free; a separate
scalar jet foundation adds formal IBP descent. Neither supplies an enumeration
of all EFT operators. See the [result guide](RESULTS_AND_SCOPE.md).

## Coefficient-space decomposition

For fermion degree n and boson degree m, extraction and reconstruction give

$$
\left(\Lambda^n V_{\mathrm{ferm}}\otimes\mathrm{Sym}^m V_{\mathrm{bos}}\right)^{*\,G\times H}
\simeq\prod_{c\in\mathrm{Content}(n,m)}\mathrm{Hom}_H(Q_c,\mathbb C),
\qquad Q_c=\big((L_c)_G\otimes M_c\big)/R_{\mathrm{exchange}}.
$$

Here G is the local group, H the residual group, L_c the local tensor source
and M_c the multiplicity carrier. The quotient transports the actual exchange
relations. Groups are abstract; compactness, semisimplicity and finite-dimensional
multiplicities are not universal assumptions. Support predicates must respect
exchange. Across all degrees the dual of the direct sum gives a product.
The equivalence does not decide arbitrary residual Hom spaces.

See [coefficient decomposition](core/Math/GRADED_OPERATOR_COMPLETENESS.md),
[relation completeness](core/Math/RELATION_COMPLETENESS.md), and
[precise hypotheses](inputs/Math/ASSUMPTIONS.md#all-degree-coefficient-space-decomposition-for-derivative-free-operators).

Related explicit-basis methods include [Li et al., JHEP 04 (2022) 140](https://arxiv.org/abs/2201.04639v2)
and [Henning et al., JHEP 10 (2017) 199](https://arxiv.org/abs/1706.08520v1).
Their on-shell/EOM/IBP frameworks are not the coefficient quotient above.
[AutoEFT, Harlander–Schaaf (2024)](https://arxiv.org/abs/2309.15783v2) is related
software, with no output comparison or formal certification here.

## Scalar jets and formal IBP

The [scalar jet theorem](core/Math/SCALAR_JET_IBP.md) constructs ordinary
commuting total derivatives, joint field/derivative grades and the actual
divergence relation range. Fixed grades are finite-dimensional for finite
component/direction types. Coefficients annihilating divergences descend
bijectively to residual Hom on the quotient, with a local-invariance wrapper
for commuting component-permutation actions. A complete quadratic example
has quotient dimension one. Mixed Bose/Fermi integration, spacetime symmetry,
EOM and analytic integrated-action equality remain separate boundaries.

## Symmetry extension and restriction

Given j:K→H on the same fields and selected domain, every K-invariant
coefficient is H-invariant exactly when restriction is surjective:

$$
\mathrm{res}_j:\mathcal C^H\longrightarrow\mathcal C^K,
\qquad \text{symmetry extension}\iff\mathrm{Surjective}(\mathrm{res}_j).
$$

Restriction is injective; injectivity alone does not imply the criterion.
The result holds degreewise and over all degrees. All finite engineering
bounds together recover the all-degree criterion; no single uniform cutoff
is asserted. Subgroup restriction transports allowance to smaller symmetries
and prohibition to larger ones on the certified common domain.

See [symmetry extension](core/Math/ALL_DEGREE_SYMMETRY_PROTECTION.md) and
[naturality and restriction](core/Math/GRADED_COMPLETENESS_NATURALITY.md).

[Grinstein, Lu, Miró and Quílez (2025)](https://arxiv.org/abs/2412.05359v1)
study all-order non-derivative accidental symmetries via friendship. Their
bosonic criterion and fermionic caveat do not supply a theorem equating
friendship with this restriction criterion. See the
[inspected source locations](../../topics/all-degree-symmetry-protection/references.md#r1--all-order-accidental-symmetries).

## Charge selection

If an actual symmetry element acts on a selected coefficient domain by a
scalar different from one, every invariant coefficient vanishes:

$$
\rho_c(h)=\chi_c(h)\,\mathrm{id},\quad\chi_c(h)\ne1
\quad\Longrightarrow\quad\mathcal C_c^H=0.
$$

The scalar must follow from field actions and survive the local and exchange
quotients. Neutral labels alone do not provide an invariant witness. Charges
may belong to any additive abelian group; cyclic and circle specializations
are proved. LFV requires a specified flavor action or transition selector.

See [selection statements](../../topics/all-degree-symmetry-protection/results.md)
and [core dossier index](core/README.md). General friendship and generic
spurion saturation remain at their recorded feasibility boundary.

## Mathematical background and further reading

The [finite-group spurion evaluation theorem](core/Math/FINITE_GROUP_SPURION_EVALUATION.md)
proves that polynomial covariants evaluate onto the actual stabilizer's fixed
space at every value, for finite groups and finite-dimensional complex
representations. Total spurion degree at most the orbit size minus one
(hence at most the group order minus one) suffices. Its dual consumer recovers
every residual invariant coefficient within the same bound. This is separate
from the general-group feasibility boundary and from EFT mass dimension.

- [Mac Lane, *Categories for the Working Mathematician*, second edition](https://link.springer.com/book/10.1007/978-1-4757-4721-8): universal constructions and adjoints provide background language for quotient/Hom descent; no particular Lean theorem is attributed to the book.
- [Fulton–Harris, *Representation Theory: A First Course*](https://link.springer.com/book/10.1007/978-1-4612-0979-9): symmetric-group representations and Weyl's construction provide tensor-statistics background.
- [Lehman–Martin, *Hilbert Series for Constructing Lagrangians*](https://arxiv.org/abs/1503.07537): invariant counting context, not a numerical oracle or premise of decomposition.
- [Joyal, *Une théorie combinatoire des séries formelles*](https://www.sciencedirect.com/science/article/pii/0001870881900529): optional labelled-structure analogy. A field-species alphabet here is not itself a Joyal species functor; no species-theoretic implementation is claimed.

The [related-literature map](../RELATED_LITERATURE.md) records roles and
inspection limits. These references establish neither priority nor a semantic
comparison theorem and introduce no external premises.
