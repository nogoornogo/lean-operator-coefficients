# Finite constituent continuation

User authorization: continue the algebraic proof through the finite nonsinglet
range. Resume `proof/sm-computable-characters` at `checkpoint 01`, with topic base
`checkpoint 02` and integration target `master`. No merge or push is authorized.
This reopens the representation-branching gate in
[the previous stopping decision](signed-mixed-stop.md).

## Frozen endpoint and interfaces

1. Connect an actual finite semisimple decomposition to coefficient support:
   for an irreducible target, a nonzero Hom exists exactly when one of the
   finitely many source blocks is equivalent to that target. Prove a symbolic
   bound on the number of blocks; do not expand the exterior basis or compute
   dimensions, multiplicities or ranks at closed content values.
   For two tensor factors, prove the necessary-and-sufficient matching test
   between their blocks and dual blocks, retaining nonsinglets of both sides.
2. Use pinned TauCeti's already-proved SU2 exhaustion, existing compact complete
   reducibility, and the proved torus bound to construct a complete finite SU2
   decomposition with every symmetric-power label in `Fin (N+1)`. This includes
   nonsinglets and repeated copies. Neither branching nor completeness may be
   supplied as a new assumption. A restriction to one group factor does not
   preserve the other factors automatically; retain that applicability limit.
   Prove that coupling two such complete SU2 sums is possible exactly when
   they share a label, without computing the number of matching copies.
3. Apply the finite-block criterion to the actual combined compact SM source
   and the Higgs constituent. Construct the decomposition from the existing
   continuous finite model, prove Higgs irreducibility, and transport the iff
   to actual local coefficients and all-degree scalar cyclic q/l requests.
   Keep the original exterior statistics and independent spin actions.

The result is a complete **finite constituent criterion**, not an executable
classifier or an evaluated highest-weight branching rule for every mixed
content. In particular, an unevaluated representation-equivalence test is
not a decided support entry. Document that distinction at every consumer.

## Allowed routes and stopping conditions

Reuse `FiniteSemisimpleDecomposition`, `DirectSumResidualHom`, Schur's lemma,
`CompactIrreducibleQuotient`, `BoundedTorusWeights`, and pinned TauCeti's
`SU2/Exhaustion`. No new dependency, literature premise, general Schur or
Kronecker theory, physical scope, closed numerical certificate or numerical
oracle is introduced. If concrete joint color/weak/spin branching and
multiplicity-space positivity still require a new theorem-level interface,
record that exact remaining prerequisite after completing these connections.

Acceptance requires focused builds, strict transitive axiom/import audits,
layout/link/diff checks and a guarded default build. Keep serialized Lean
execution with one thread, the existing 6 GiB sampled process-group threshold,
4 GiB host reserve and unchanged 300-second timeout. An unchanged root-import
resource failure remains an outstanding build gate, not permission to rebuild
retired numerical certificates or raise the resource budget.

## Recorded outcome

All three theorem connections above are proved, including complete bounded
SU2 sums and finite nonsinglet block coupling. The actual mixed q/l consumer
retains unevaluated block-equivalence tests. The next labeled joint exterior
occurrence prerequisite is recorded in [results](finite-branching-results.md).
Focused strict audits and the Math/Physics aggregates pass; the default GUT
aggregate remains outside the unchanged sampled memory threshold. Overall
build acceptance and arbitrary mixed classification are not marked complete.
See [verification](finite-branching-verification.md).
