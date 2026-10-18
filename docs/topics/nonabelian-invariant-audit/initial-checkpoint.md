# Initial Algebraic Checkpoint

This checkpoint does not complete the finite-group audit or prove a non-Abelian
proton-selection-rule theorem. The working branch remains separate from master.

## Nonzero Coefficient

[InvariantPairing](../../../Math/RepresentationTheory/InvariantPairing.lean)
constructs an intertwiner to the trivial representation:

```
((V tensor V*) tensor (W tensor W*)) -> k
(x tensor f) tensor (y tensor l) |-> f(x) * l(y)
```

- `evaluation`: the ordinary evaluation map is equivariant.
- `pairedCoefficient`: tensor two evaluations and use the scalar tensor unit.
- `pairedCoefficient_invariant`: invariance on every tensor, not only pure ones.
- `exists_pairedCoefficient_eq_one`: a pure tensor evaluates to one when V,W
  are nonzero; therefore the invariant functional is nonzero.
- `pairedCoefficient_ne_zero`: the resulting intertwiner is nonzero.

The group can be arbitrary, not necessarily finite, Abelian or compact. Neither
unitarity nor finite-dimensionality is needed for this algebraic construction.
It is an element of the dual tensor space (an invariant coefficient functional).
It must not silently be described as a vector in the original tensor product.
Reordering it into the physical field order or restricting it to light fields
requires the corresponding equivariant maps; these are not supplied here.

## Actual Mass And Conjugation

[ConjugationMassIndex](../../../Physics/FieldTheory/Mass/ConjugationMassIndex.lean)
proves, for a finite-dimensional complex representation rho of G, a homomorphism
j from K to G, a homomorphism a from K to itself, and n in G with
`j(a(x)) = n * j(x) * n^-1`:

```
chi_radical(a(x)) - chi_radical_dual(a(x))
  = chi_radical(x) - chi_radical_dual(x).
```

The mass is symmetric and invariant under the restricted K representation.
The proof first uses `SymmetricMass.radical_dual_character_eq`, then ambient
character conjugacy. It does not restrict n to the radical and does not assume
that n preserves the mass. `radical_dual_character_invariant_prod` retains any
commuting residual group H and establishes the identity for every `(t,h)`.
No `CommGroup H`, source Laurent model or light-profile condition is needed.

## Open Light-Spectrum Interface

The following implications have NOT been proved in this checkpoint:

1. Extract residual H-module information at the monitored torus weights from
   the actual light dual-character identity, without scalar H-charge labels.
2. Formulate the non-Abelian analogue of the positive local target and derive
   the shared positive representation content of Q/u/e and down/lepton.
3. Realize the needed modules inside the actual light sector and transport
   the nonzero coefficient without losing nonzeroness. A character identity
   alone is not such a realization.

For finite complex representations semisimplicity is a plausible route, but
its application to these concrete modules is an obligation, not a premise to
hide in a certificate. The S3/A4 controls will test this interface. An arbitrary
choice of five unrelated flavor representations is not a counterexample to
the retained UV assumptions.

## Persistent Audits

- [Pairing audit](../../../Math/RepresentationTheory/Audit/AuditInvariantPairing.lean):
  six declarations and Math import boundary.
- [Mass/conjugation audit](../../../Physics/FieldTheory/Mass/Audit/AuditConjugationMassIndex.lean):
  two declarations and Physics import boundary.

Both use strict transitive axiom collection. No `sorry`, custom axiom,
`native_decide` exemption, new dependency or literature premise is introduced.
