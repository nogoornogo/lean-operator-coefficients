# S3 And A4 Controls

NA-2 is a bounded exact test of the representation interface, not an exhaustive
classification of assignments or a search through physical UV models.

## Actual Representations

[FiniteFlavorControls](../../../Math/RepresentationTheory/FiniteFlavorControls.lean)
defines the permutation action on complex coordinate functions by
`rho(g)(x)(i) = x(g^-1(i))`. Coordinate sum is an actual intertwiner to the
trivial representation. Its kernel is therefore an invariant subspace.

| Group | Space | Checked complex dimension |
| --- | --- | --- |
| S3 = permutations of Fin 3 | sum-zero functions on Fin 3 | 2 |
| A4 = even permutations of Fin 4 | sum-zero functions on Fin 4 | 3 |

The dimensions follow from rank-nullity and surjectivity of coordinate sum,
not from an assumed character table. Noncommuting elements are exhibited in
both groups. The formula `sum star(x_i) * y_i` is preserved on the subspace;
no approximation or external numerical calculation is used.

## Positive Controls

For each actual representation R, the ordered coefficient functional on
`(R tensor R*) tensor (R tensor R*)` is equivariant and nonzero. The witness
comes from two evaluations, with the contragredient action on each dual factor.
This tests the generic construction on genuine non-Abelian examples.

These are invariant functionals, not a count of all invariant vectors, and
not physical operators after Grassmann or Lorentz identities.

## Negative Controls

Every equivariant linear functional from R to the trivial representation is
zero. A spanning family consists of coordinate differences. In S3 a swap,
and in A4 a double swap, reverses each nonzero spanning difference. Invariance
then forces its image to vanish over the complex numbers.

Tensoring R with three trivial scalar representations does not change this:
`((R tensor 1) tensor 1) tensor 1` has no nonzero invariant coefficient.
The proof uses actual tensor-unit equivariant isomorphisms.

This supplies a four-factor negative control with nonzero field spaces. It
shows why dual matching cannot be discarded from the general pairing argument.
It is NOT a counterexample under the UV conjugation, mass and light-target
conditions: no such source is supplied for this unmatched assignment.

## Coverage And Remaining Work

- Tested: these two concrete sum-zero representations and the two specified
  four-factor patterns, plus their invariant-linear-functional controls.
- Not tested: all irreducible/reducible assignments of dimension at most 3,
  all complex one-dimensional A4 representations, anomaly constraints,
  arbitrary masses, or physically admissible UV completions.
- Irreducibility classification is not used or claimed as a formal result.
- The tests do not establish absence of a physical counterexample. NA-3 must
  still derive the needed matched content from the retained light conditions.

The [persistent audit](../../../Math/RepresentationTheory/Audit/AuditFiniteFlavorControls.lean)
checks 13 declarations transitively against the standard three-axiom allowlist
and enforces the Math import boundary. No native computation axiom is allowed.
