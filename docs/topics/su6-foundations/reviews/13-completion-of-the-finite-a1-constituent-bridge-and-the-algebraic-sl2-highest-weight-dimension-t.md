# completion of the finite A1 constituent bridge and the algebraic sl2 highest-weight dimension theorem

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

### stage 01 / Codex / Lean 4.33.1

- Scope: completion of the finite A1 constituent bridge and the algebraic
  `sl2` highest-weight dimension theorem
- Local-model role: none

### Audit result

The following additional stages now kernel-check:

- finite extraction of all simple constituents of the semisimple restricted
  defining representation;
- classification of each constituent by continuous product factorization and
  the explicit highest-weight interface;
- transport of the weak-center sign from each weak factor to its ambient
  constituent and exclusion of `(3,1)+(1,3)` by injectivity;
- recognition that the `(3,2)` constituent fills the entire six-dimensional
  representation and is therefore irreducible;
- equivalence of the Euclidean and ordinary defining-representation models;
- exclusion of `(3,2)` by a nontrivial commuting continuous hypercharge circle;
- linear independence, invariance, spanning, and the dimension formula for
  the lowering string of an irreducible complex `sl2` module.

Consequently,
`A1DecompositionBridge.injectiveEmbedding_with_hypercharge_has_weakDoubletBranch`
proves the standard branch-count conclusion conditional only on
`SU2SU3HighestWeightTheory`.  The sharper
`SU2LieSU3HighestWeightTheory` derives the `SU(2)` dimension formula from the
new `Sl2String` theorem.  Remaining inputs are the continuous group-to-Lie and
center-exponential bridge for `SU(2)`, the A2 highest-weight theorem for
`SU(3)`, and a separate conjugacy/source-automorphism classification.

The full build completed successfully with 3776 jobs.  The source tree has no
`sorry`, `admit`, or declared `axiom`.

---
