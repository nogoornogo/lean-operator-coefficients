# Verified Master Integration

The user explicitly authorized merging the present verification results,
leaving further theory work for later consideration. The worktree was clean;
master had no independent changes relative to the topic. The preserved-history
command `git merge --no-ff proof/derivative-literature-comparison` completed
without conflicts. The merged tree equals the checked topic tree. No proof,
hypothesis, source pin or comparison boundary changed during integration.

## Merged-State Verification

The topic's focused gate passed before integration and again on master:

```sh
LEAN_NUM_THREADS=2 lake build Math.RepresentationTheory.Audit.AuditDerivativeLiterature Physics.FieldTheory.Jets.Audit.AuditDerivativeLiterature
LEAN_NUM_THREADS=2 lake build
python3 tools/derivative-literature/check-one-dimensional.py
python3 tools/derivative-literature/check-scalar-lorentz.py
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

Focused verification passes 3308 jobs and 147 strict transitive declaration
checks, 71 Math and 76 Physics. The serialized full build passes 7697 jobs.
Both retain the 16 GiB per-process address-space guard, two threads and
default Lean elaboration limits, with focused/full wall-clock guards of
180/540 seconds. No new-source warning appears; inherited dependency and
module-system advisories remain. Existing audit allowances are unchanged.

Both independent exact diagnostics pass again on master. They remain
supplementary computations, without an assumed Lean semantic/group bridge.
Layout passes 2203 modules; topic navigation passes 158 indexed topics and
158 outcomes with no pending exception. Metadata, local links and diff checks
pass after the integration documentation update. These documentation edits
do not establish a further Lean proof baseline.

## Preserved Result Boundary

C1–C5 remain partial comparisons with the explicit gaps in
[results](results.md) and [routes](route-review.md). C6 proves the specified
quartic scalar helper/direct-input and polynomial-substitution contract.
No complete derivative SMEFT basis, paper-wide verification or analytic
field-redefinition equivalence is asserted.

The final source roles agree across the topic register, shared bibliography,
coverage ledger, proof dossier and assumptions. Published nonderivative
interfaces, dependency pins and the root README are unchanged. The user has
not authorized implementation of the remaining foundations by this merge.

## Local Branch Retirement

The local topic branch is retired with `git branch -d` after confirming its
HEAD is reachable from master, no worktree uses it and no pending child
needs it. The historical branch name remains in the topic record. Unrelated
branches/worktrees are retained. No push or remote branch deletion is made.
