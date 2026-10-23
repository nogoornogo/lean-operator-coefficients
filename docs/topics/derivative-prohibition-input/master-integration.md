# Master Integration

## Authorization And Scope

The user explicitly requested merging the present topic state. The recorded
target is master. The integrated branch `proof/derivative-prohibition-input`
includes the completed A–D proof contract and its already integrated bounded
child `docs/derivative-input-literature-review`.

The worktree was clean, master had not advanced beyond the topic base,
and no other worktree used master. The preserved-history merge
`git merge --no-ff proof/derivative-prohibition-input` completed without
conflicts. Its resulting tree agreed with the verified topic tree before
the integration documentation changes.

## Proof Gates

The following focused gate passes before the merge and again on master:

```sh
LEAN_NUM_THREADS=2 lake build Math.RepresentationTheory.Audit.AuditDerivativeProhibition Physics.FieldTheory.Jets.Audit.AuditScalarProhibitionConditions Math.RepresentationTheory.Audit.AuditDerivativeInputAdapters Physics.FieldTheory.Jets.Audit.AuditInputAdapter
```

Each invocation passes 3877 jobs and 269 strict transitive declaration
checks: 37 common criteria, 33 scalar controls, 33 selection counterexample,
9 Lorentz scalar parameter declarations and 125/32 existing Math/Physics
adapter declarations. The new namespace inventories include definitions,
instances and generated helpers and must be nonempty. Math rejects
Physics/GUT imports; Physics rejects GUT imports. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted transitively.

After the merged-state focused gate, one serialized full build passes:

```sh
LEAN_NUM_THREADS=2 lake build
```

The merged full build passes 7703 jobs. Both gates retain the 16 GiB
inherited per-process address-space guard, two threads, 180/540-second
focused/full ceilings and default Lean elaboration limits. No cap is raised.
There are no new-source warnings; inherited module-system advisories remain.
Subsequent changes are integration documentation only and do not rerun or
replace these proof gates.

## Assumptions And Literature Reconciliation

The [results](results.md), proof dossier and assumption ledgers retain
actual quotient support, explicit scalar action or semisimplicity and the
selected restriction-surjectivity premise. The cubic coupling condition
is necessary for the specified nonzero evaluation, without an existence
claim at zero coupling or whole-model classification.

The [six-paper usage review](../derivative-input-literature-review/review.md)
is documentation based on existing theorems. The shared
[bibliography](../../proof/RELATED_LITERATURE.md),
[source registers](references.md) and
[coverage ledger](../../verification/derivative-interface-coverage.md)
are reconciled. C1–C5 remain partial and C6 retains its constructed finite
polynomial scope. No paper premise, new physical dictionary or complete
literature basis is introduced by the survey or this integration.

Published input signatures, dependency pins and existing audit policies
remain unchanged. No unrelated dirty work or worktree is integrated.

## Repository Gates And Cleanup

```sh
node tools/layout/check-layout.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
node tools/docs/check-links.mjs
git diff --check
```

All merged-state gates pass: 2209 modules with valid layers, imports and
aggregate coverage; 160 indexed topics and outcomes, without a pending
exception; 1204 portable documents/evidence files; 1212 Markdown files with
7695 local inline links and 143 heading fragments, zero errors. Whitespace
checks pass. The local-link checker runs unchanged with its required Git
subprocess permitted.

The local topic branch is retired with ordinary `git branch -d` after
confirming its HEAD is reachable from master, no worktree uses it and no
child work still needs it as an integration target. The earlier child was
already integrated and retired. Historical branch names remain in the
topic records. No remote update, remote branch deletion or unrelated
worktree cleanup is performed.
