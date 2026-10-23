# Jet/Spurion Connection Verification

The parent derivative/IBP and finite-group spurion baselines are retained in
their own topics. This file records only checks run for the connection.

## Planning Checkpoint

The starting tree was clean on the completed derivative/IBP topic. The new
child branch is `proof/jet-spurion-evaluation`, targeting `proof/derivative-ibp`.
The [contract](plan.md) freezes the statement, assumptions, actual quotient
interfaces, positive-derivative consumer, resources and stopping conditions.
No source result or new build baseline is claimed by this checkpoint.

## Proved Endpoint

The [frozen contract](plan.md) is fulfilled by the [actual connections](results.md).
The primary local-coinvariant composition route succeeds; no fallback source,
extra completeness assumption or foundational extension is needed. Scalar
EOM/IBP and mixed off-shell IBP evaluation retain both degree cutoffs. The
massless scalar consumer uses the actual four-dimensional local action. The
complete mixed sign example proves the full induced action, nonzero-value
coefficient, zero-value prohibition and sharp degree-one control on its actual
nonzero derivative quotient. Original representative evaluation and injective
coefficient pullbacks are checked.

Focused command:

```sh
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditJetSpurionEvaluation Physics.FieldTheory.Jets.Audit.AuditLorentzSpurionEvaluation
```

The focused closure passes **3416 jobs**. The Math audit checks **87** named
declarations and the physical audit **10**, **97** total, transitively. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted. The Math audit
rejects Physics/GUT imports and the physical audit rejects GUT imports.
All new public declarations have explicit audit entries; the new maps also
audit their inherited proof dependencies. No audit policy is changed.

Full aggregate command:

```sh
LEAN_NUM_THREADS=4 lake build
```

It passes **7618 jobs**, retaining all parent Math, Physics, GUT and audit
targets. Heavy commands use a 540-second timeout, four Lean threads and an
inherited 16 GiB per-process address-space limit (`resource.RLIMIT_AS`). This
is an enforced guard, not measured peak memory. Disposable logs and the guard
wrapper remain outside source control. Default heartbeats, recursion/kernel
limits and all root/docbuild dependency pins remain unchanged. Explicit local
carrier instances and direct stability on derivative generators resolve
adapter elaboration. New-module residual warnings are module-system
recommendations; existing project warnings remain. No `sorry`, custom axiom,
literature completeness premise or allowlist exception is introduced.

## Structural, Documentation And Final Review

- `node tools/layout/check-layout.mjs`: **2124 modules**, with layers, local
  imports, cycles, aggregate coverage and relocation audits passing.
- `node tools/docs/check-links.mjs`: **1130 Markdown files**, **7191** local
  inline links, **125** fragments, zero errors. The unchanged checker was
  rerun in a permitted context after sandbox `spawnSync git EPERM`.
- `python3 tools/docs/check-topic-index.py`: **149 topics**, all indexed
  and linked to outcomes; no pending exception.
- `python3 tools/docs/check-work-metadata.py`: **1122** portable documents
  and evidence files, no work-history exemptions; source metadata retained.
- `git diff --check`: passes. Root/docbuild toolchain and dependency-pin diff
  is empty. No imported audit or existing proof is relaxed.

The final bibliography and Math/Physics assumptions distinguish the actual
fixed-grade source connections from the excluded general-group and physical
claims. No literature-comparison coverage row is added. Documentation follows
the proof checks and changes no theorem or environment. The verified stop is
recorded on `proof/jet-spurion-evaluation`, targeting its unmerged parent
`proof/derivative-ibp`. Parent/master merge and remote push are not performed.

## Parent Integration

Explicit user direction authorizes integration into `proof/derivative-ibp`.
The clean child was merged with `git merge --no-ff`; the parent had not
advanced independently and the merge had no conflicts. Merged-state focused
audits pass 3416 jobs, including 87 Math and 10 physical strict checks.
Merged-state full `lake build` passes 7618 jobs under the same guard. Layout
passes 2124 modules; topic/portable-metadata and link/diff checks pass.
The final source roles were already reconciled into RELATED_LITERATURE before
integration. No proof, pin or audit policy changes during the merge.
Integration-record edits are documentation only; no additional Lean build
is rerun for those edits. The local child was safely deleted after confirming
reachability, no attached worktree and no unfinished child work. Its historical
branch name is retained in the topic record. Master integration and push are
not performed.
