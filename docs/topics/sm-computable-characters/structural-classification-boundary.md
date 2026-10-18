# Remaining partially occupied mixed-source classification

This records a mathematical interface boundary, not a memory failure, a
counterexample to classification, or completion of the original stage 2.
The user subsequently reopened a construction limited to the fixed SM
representations, with external literature premises as a last resort. The
[new plan](limited-foundation-plan.md) and [first proved foundation](limited-foundation-results.md)
supersede the stopping decision below; the unproved occurrence problem remains.
The [new structural results](structural-classification-results.md) actually
decide additional mixed regions; the previous 48-term coefficient criterion
continues to apply conditionally elsewhere but is not counted as a decision.

## What is still required

For each actual signed species s and a fitting exterior degree d, supply a
complete joint decomposition of

```text
Lambda^d ((GaugeCarrier_s tensor Spin_side(s)) tensor Flavor_3)
```

into color highest-weight representations, weak symmetric-power labels and
the two independent spin labels, with an explicit **positive occurrence
criterion** for its multiplicity spaces. It must be proved on the actual
exterior representation, including the three-generation restriction. A
torus-character identity, an unevaluated Kronecker coefficient, a matching
Hom, or the nonzero sign of a signed coefficient sum is not that criterion.
Then prove the cross-species color couplings and SU2 triangle/parity rules
are compatible with those actual occurring components. This must give both
witnesses for permission and exclusions for prohibition.

An equivalent direct proof of the actual joint color-trivial, spin-zero
source support would also suffice. Complete colored branching is one
sufficient route, not a logical requirement to catalogue irrelevant targets.
One may not require a separate singlet in every species: the existing QQQL
counterexample rules out that proposed necessary condition.

The general case left here is a fitting partially occupied mixed source;
capacity, charge, centers and the new complementary weak bound do not by
themselves prove simultaneous occurrence. Nothing in this record asserts
that those necessary conditions are sufficient or that all residual unknown
cases are forbidden. Balanced signed counts prove charge neutrality only,
except in the saturated subfamily where the full iff is now proved.

## Pinned Lean APIs checked again

The following local pinned sources were inspected, without changing pins:

- `TauCeti/RepresentationTheory/ClassicalGroups/WeylModule/SchurWeyl.lean`
  proves the character decomposition of a tensor power under GL, explicitly
  described as the character shadow of Schur--Weyl decomposition. It does
  not construct the joint exterior support above or decide its positivity.
- `.../WeylModule/Multiplicity.lean` identifies a symmetric-group
  Young-symmetrizer-ideal Hom with a GL Weyl module and proves nonvanishing
  iff its diagram has at most the ambient number of rows. Its target is a
  tensor power. This row criterion is not a singlet-branching criterion for
  a tensor-product subgroup acting on an exterior power.
- `.../WeylModule/SpecialLinear.lean` constructs determinant-twist restriction
  to SL. Its header explicitly says irreducibility and exhaustion of the
  restricted representations are not proved there. Restriction to the
  actual compact source and compatibility with its tensor factors remain
  additional obligations.

Targeted searches in the pinned representation/combinatorics sources did not
find a ready general Kronecker-positivity or skew-Cauchy support API matching
this interface. This is a scoped search result, not proof of absence of any
possible Lean solution. The previous external-library assessment remains
[available](support-structure-assessment.md#lean-availability-at-inspected-revisions).

## Additional primary literature inspected

1. [Manivel, *A note on certain Kronecker coefficients*, arXiv:0809.3710v1,
   Theorem 1 and Section 2](https://arxiv.org/html/0809.3710v1).
   Theorem 1 gives a positive multiplicity-free decomposition of the tensor
   square of the two-row rectangle `[n,n]`: diagrams of even parts and length
   at most four, plus diagrams of odd parts and length exactly four.
   Section 2 explains the Schur--Weyl connection to tensor-product subgroups.
   The equal two-row rectangle hypothesis is substantial: a general weak
   label, the color factor, flavor factor and mixed-species tensor couplings
   are not all covered by this one tensor-square rule. It is a candidate
   special-case input, not an assumed rule for arbitrary SM contents.
2. [Ikenmeyer--Panova, *Rectangular Kronecker coefficients and plethysms in
   geometric complexity theory*, arXiv:1512.03798v2,
   Section 4 (especially Theorem 4.7)](https://arxiv.org/html/1512.03798v2).
   Its hypotheses include `ell = max(length(nu)+1,9)`, `a > 3*ell^(3/2)`,
   `b >= 3*ell^2` and `size(nu) <= a*b/6`, with an excluded-shape condition.
   The resulting rectangle degree `a*b` is already beyond the present total
   fermion-capacity bound when `ell >= 9`; this theorem cannot simply be
   applied to the exact small-degree source by stretching it. The paper also
   treats other special families. Its limit/stretching conclusions must be
   distinguished from the exact coefficient needed here. No general coverage
   of the fixed three-generation mixed exterior source has been established.

These are established special-case theorems, not evidence that the present
fixed SM classification is impossible or equivalent to every general
Kronecker problem. No new literature premise, source copy or dependency is
introduced by this inspection. The new Lean results use neither theorem.

## Why the continuation stops at this interface

The remaining work requires constructing and proving a new general joint
branching/positive-support foundation, or identifying and specializing a
sufficient existing theorem covering the actual remaining family. The
currently inspected special rules do not discharge it. Introducing an
assumption of its desired positive support would assume the very part the
user asked to prove, and expanding the old numerical character tables would
violate the user's instruction.

The repository rule in [AGENTS.md](../../../AGENTS.md) is: “Do not silently
add assumptions or recursively start a new foundational project.” Accordingly
the exact foundation is recorded here and left unproved. This is the genuine
gate in stage 3 of this pass; the classified saturated region and the proved
uniform exclusions remain valid. The original full q/l support classification
remains unfinished.
