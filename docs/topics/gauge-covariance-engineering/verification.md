# Verification

Working branch: `proof/gauge-covariance-engineering`; integration target:
`proof/nonlinear-eom-gauge-jets`, under the bounded-child exception. The initial
parent worktree was clean. No parent/master integration or remote mutation
is included. The Lagrangian and first-variation deferral remains in force.

## Frozen Statements And Focused Gate

The contract was recorded before implementation and all three stages close
through their primary routes: associative unit identities, trace cyclicity,
positive engineering weights and a full-relation coefficient functional.
No new independent foundation, external covariance/counting premise, custom
axiom, dependency pin or audit allowlist exception is introduced.

```sh
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditGaugeEngineering Physics.FieldTheory.Jets.Audit.AuditGaugeEngineering
```

Passed: 3289 jobs, with 48 Math and 40 physical public declaration checks,
88 total. The persistent audits explicitly inventory all named public
definitions, abbreviations, theorems and instances in the eight implementation
files and collect axioms transitively. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. The Math audit rejects Physics/GUT imports; the
physical audit rejects GUT imports. All ten new implementation/audit modules
are registered in the appropriate aggregates.

The audited controls include a nonconstant polynomial unit with nonzero
derivative and nonzero flat transformed connection, actual transformed
Yang–Mills equations in the full EOM ideal, trace IBP in the actual quotient,
engineering degrees of the actual scalar/matrix equations, complete scalar
source reconstruction, annihilation of the full unbounded EOM ideal and
divergence range, a nonzero square class, inverse coordinate equivalence,
singleton basis and exact dimension one for every complex coupling.

Explicit trace cyclic rewrites avoid recursive simp orientation; typed
entrywise maps and source equalities resolve elaboration without raising
heartbeats, recursion/kernel limits or changing theorem hypotheses. The final
focused run has no new linter/deprecation warnings; new residual warnings
are module-system import recommendations. Existing project warnings remain.

## Full Build And Structural Gate

```sh
LEAN_NUM_THREADS=4 lake build
node tools/layout/check-layout.mjs
```

The final full build passes 7663 jobs, including Math, Physics, GUT and all
old/new persistent audits. Layout passes for 2169 modules, with layers,
local imports, cycles, aggregate coverage and relocation audits.

Heavy checks are serialized with four Lean threads, a 540-second command
timeout and an inherited 16 GiB per-process address-space guard. This is a
resource guard, not a measured universal memory bound or an elapsed-time
estimate. Disposable logs and the guard wrapper remain outside source control.
Root README, all dependency pins and existing proof/audit sources are unchanged;
the aggregate import lists register the new modules.

## Documentation And Final Review

```sh
node tools/docs/check-links.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
git diff --check
```

The actual statements, source register, mathematical/physical dossiers and
assumption ledgers agree. The bibliography records final source roles and
result links before any future integration. No literature-comparison coverage
row is warranted. Algebraic unit formulas do not assert a local gauge orbit
quotient or a polynomial automorphism of the connection-only ring. The exact
scalar count concerns one engineering-degree-two image in the full EOM/IBP
source; it is not a general matrix invariant basis or quotient grading.

Final documentation gates pass: 1162 Markdown files, 7408 local inline links,
125 heading fragments and zero link errors. The unchanged link checker runs
where its read-only Git subprocess is permitted. All 154 topics have indexed
outcomes, with no pending exceptions. Portable metadata passes for 1154 files.
The diff is whitespace-clean; root README, dependency pins and coverage
ledgers are unchanged. Both explicit audit inventories match all named public
declarations in the eight implementation files.

Final status and source records after the successful proof gates are
documentation only; no further Lean build is run for those edits. The
successful stop is the verified three-stage contract on the child branch.
No Lagrangian/first-variation derivation, parent/master merge, remote update
or new foundational topic is started at this stop.

## Final Master Integration

The [merged-state record](../derivative-ibp/master-integration.md) supersedes
the earlier unmerged integration status. The original proof endpoints and
checks above remain checkpoint evidence; all recorded parent merges and the
master merge are verified without changing theorem assumptions.
