# Actual exterior-doublet weight slices

Continuation from `checkpoint 01` on `proof/sm-computable-characters`, integration
target `master`; no merge or push authorized. This closes the exterior-source
comparison in step 3 of the [completion plan](colored-support-completion-plan.md).
It does not yet finish Q degree-five/six branching or original endpoint 2.

## Uniform source theorem

For any complex representation s of any retained group K on A,
`SU2ExteriorWeightSlice.equivalence s p q` proves a K-equivariant equivalence

```text
Weight_(p-q) (Lambda^(p+q) (doublet external s))
  = Lambda^p(s) tensor Lambda^q(s).
```

The source is the actual exterior representation, and weight means the
eigencondition for the entire fixed SU2 circle. Both directions retain every
action on A. There is no finite-dimensionality, continuity, semisimplicity,
irreducibility, Weyl formula or branching premise in this theorem.

## Construction

- `TorusScalarProductSlice` extracts a unique scalar-weight summand from
  a complete product; coordinates of different weights vanish by the full
  circle-character distinction. Its inverse is the actual single inclusion.
- `PatternScalarWeights` descends the sum of species weights through the
  statistical image, and identifies that exponent with the occupation-weight
  sum. This is an identity of actions on vectors.
- `BinaryScalarExteriorSlice` proves that fixed total degree and opposite
  scalar weights determine both occupations uniquely. The complete occupation
  equivalence and the existing binary exterior equivalence then identify the
  weight space with the tensor of two exterior powers. The proof is uniform
  in p and q; it does not enumerate words or occupations.
- `SU2DoubletTorusSplit` identifies the circle restriction of the actual
  doublet tensor A with two oppositely twisted copies of s, using the tensor
  and finite-coordinate equivalence from mathlib.
- `SU2ExteriorWeightSlice` transports actual weight spaces through that
  exterior equivalence and removes the circle twist from the retained action.

The five modules add 31 strict transitive declarations. Their imports remain
within the structural audit's numerical-evaluator exclusion. No large tensor
basis, numerical dimension, multiplicity or matrix rank is evaluated.

## Continuation boundary

Together with the [consecutive-slice theorem](spin-slice-results.md), this
provides two actual descriptions of the same spin-weight space. For Q's
dimension-six color/weak factor, the right-hand exterior degrees are already
controlled by square/cubic decompositions and complementary duality.

The remaining tasks are to resolve their tensor products into compatible
color/weak components, cancel the higher spin slices, assemble the full Q
degree-five/six equivalences, and prove the positive restricted-color coupling
criterion used by the full mixed-content q/l consumer. None of these tasks
is counted as completed merely by this source comparison.

See [verification](exterior-weight-slice-verification.md).
