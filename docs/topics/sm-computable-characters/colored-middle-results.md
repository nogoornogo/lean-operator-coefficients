# Cubic Cauchy bridge and exterior-restricted color coupling

This page records checkpoint `checkpoint 01`. The subsequent
[cubic resolution](colored-cubic-resolution-results.md) closes the hook
obligation described below and completes labelled core degrees three/nine.
Degrees four through six and general restricted-Young coupling remain open.

The [plan](colored-middle-plan.md) produces two unconditional structural
results. The complete Q middle-degree and general restricted-Young coupling
endpoints remain open. No numerical representation certificate, Weyl input,
new literature premise or dependency change is used.

## Universal cubic splitting

`ExteriorSymmetricColumn.column` constructs
`Lambda^n A tensor Sym^n B -> Lambda^n(A tensor B)` in every degree,
without a dimension hypothesis. Pure symmetric powers establish alternation
in the A slots; the map is natural in both factors.

`ExteriorCubeDoubletCauchy.equivalence` proves, for every finite-dimensional
complex A and a two-dimensional doublet S,

```text
Lambda^3(A tensor S)
  = (Lambda^3 A tensor Sym^3 S) + (Hook A tensor S).
```

Here `Hook A` is the actual kernel of exterior multiplication
`A tensor Lambda^2 A -> Lambda^3 A`. A universal top-column retraction and
the already proved hook retraction prove that the two embeddings are
independent. Exhaustion follows from the universal hook split and standard
functor dimension formulas. `binomial_identity` proves the required identity
for arbitrary dimension n and hook dimension k; no Q dimension, invariant
multiplicity or matrix rank is evaluated. The scalars six and nine normalize
universal symmetrization/contraction maps, rather than content certificates.

`ExteriorCubeDoubletCauchyRepresentation.equivalence` retains an arbitrary
group representation on A and any pulled-back SU2 doublet. It needs neither
determinant one nor dimension three for A. This removes the obstruction to
using A = color tensor weak in the earlier cube construction.

## Actual Q and conjugate-Q coarse branches

`SU3DoubleSpinCube.positive` and `negative` combine that universal split with
the proved color/doublet cube. For defining color C, weak W and spin S, the
result is an actual equivariant equivalence

```text
Lambda^3((C tensor W) tensor S)
  = [(Sym^3 W tensor Sym^3 S)
      + ((trace-free End C tensor W) tensor Sym^3 S)]
      + (Hook(C tensor W) tensor S).
```

The conjugate result uses dual color and its actual trace-free endomorphism
action. Complementary duality gives degree nine. `SMQCubeBranching`
transports all four equivalences to actual signed core species 0 and 5,
retaining independent weak, left spin and right spin projections.

This split exhausts the cube, but **does not resolve the last hook into
color/weak-labelled components**. It is not a completed Q-cube classification,
and it supplies no new full all-Higgs q/l iff by itself. Degrees four through
six, and their unresolved complementary branches, are not inferred from it.

## Arbitrary exterior-restricted color words

`SU3ExteriorColorWord` permits arbitrary binary tensor words whose leaves are
`Lambda^n C` or `Lambda^n C*`, with arbitrary natural degrees and ordering.
Its proved quotient equivalences reduce degrees zero/three to the scalar,
one to the original defining/dual action, and two to the opposite action.
An over-capacity leaf makes the whole actual source zero.

`allowed_iff` gives a closed positive rule: all leaves must have degree at
most three, and the numbers of defining and dual leaves **after this proved
reduction** must agree modulo three. The positive direction transports the
actual evaluation/determinant witnesses. `forbidden_iff` proves both kinds
of exclusion. No unknown Hom or assumed isomorphism remains in this rule.

`SU3CompatibleCoupling.exterior_word_iff` combines this with the exact
simultaneous matching of both independent SU2 labels. It separates color
from weak/spin only after the complete source is assembled.

This closes arbitrary products of exterior-restricted defining/dual color
factors. It does **not** extend triality sufficiency to arbitrary symmetric,
trace-free or higher Young summands. Those may lose a coefficient under
projection. The full original q/l endpoint remains incomplete.

## Exact remaining foundation

The next cubic obligation is a complete color/weak decomposition of the
actual `Hook(C tensor W)`, with equivariant embeddings, projections and
inverse/exhaustion relations. Degrees four through six require the analogous
actual skew-Young splittings, retaining both SU2 factors. They cannot be
obtained by repeating the exterior-degree-two identities alone.

Pinned TauCeti's `WeylModule/SchurWeyl.lean` explicitly proves the character
shadow of Schur-Weyl decomposition. Its inspected statements do not furnish
these equivariant inverse maps. `WeylModule/SpecialLinear.lean` explicitly
leaves restriction irreducibility/exhaustion unproved; continuous Schur's
lemma assumes irreducibility rather than proving it for a proposed Young
component. None was inserted as an assumption to close this gap.

For the larger restricted color class, an actual positive tensor-product
rule for its identified Young components is still required, including
occurrence and exclusion. The new exterior-word rule is a resolved subclass,
not that missing rule. These are theorem-level prerequisites for a further
Young-projector/positive-coupling milestone; no broader highest-weight
classification project or literature-premise fallback was started silently.

See [verification](colored-middle-verification.md) for executed checks.
