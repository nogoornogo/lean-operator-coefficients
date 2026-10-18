# Milestone A: Local Coinvariants

## Established Interfaces

`LocalCoinvariantHom.equiv` constructs the residual-Hom inverse for the span
of `g • u - u`, with only commuting local/residual actions. The target may
be any residual representation, not only scalars. Pullback and descent agree
on quotient generators; total zero and existential nonzero are equivalent.
Local-compatible residual-equivariant exchange maps descend to the quotient.

`CommutingActionHom.equiv` connects the actual combined G × H coefficient
space to this quotient Hom. Its target has trivial local action.

`LocalCoinvariantTensor.relations_eq_range` proves that the relations on
`L ⊗ M`, when G acts trivially on M, are precisely the tensor extension of
the relations on L. Its linear and residual-equivariant equivalences identify
`(L_G) ⊗ M` with `(L ⊗ M)_G`. Arbitrary multiplicities are retained, without
finite-dimensionality, semisimplicity, averaging or a supplied contraction basis.

## Verification And Remaining Work

`lake build Math.RepresentationTheory.Audit.AuditLocalCoinvariants` passes
(1,726 jobs), including 19 strict transitive axiom checks. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Repository-wide checks are
Full `lake build` passes (6,488 jobs); layout passes (1,161 modules), links
pass (447 Markdown documents) and `git diff --check` passes. This does not
complete the topic: mixed
species assembly, exchange-quotient commutation, grading and SM consumers remain.

## Sources

- [Hom descent](../../../Math/RepresentationTheory/LocalCoinvariantHom.lean)
- [Tensor separation](../../../Math/RepresentationTheory/LocalCoinvariantTensor.lean)
- [Combined group connection](../../../Math/RepresentationTheory/CommutingActionHom.lean)
- [Persistent audit](../../../Math/RepresentationTheory/Audit/AuditLocalCoinvariants.lean)
