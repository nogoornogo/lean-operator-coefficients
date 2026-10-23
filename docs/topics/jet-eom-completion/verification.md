# Verification

## Environment And Scope

Branch: `proof/jet-eom-completion`; target: `proof/linear-eom-weyl` under the
recorded bounded child exception. The initial worktree was clean. No parent or
master merge, remote update, dependency pin or old proof change is included.
All seven new implementation files and two audits are registered in `Math.lean`
or `Physics.lean`. Strict audits reject forbidden source-layer imports.

Heavy checks use `LEAN_NUM_THREADS=4`, a 540-second command timeout and an
inherited 16 GiB per-process address-space guard. Default Lean heartbeats,
recursion and kernel limits remain unchanged. Temporary output stays outside
source control. No tests import a generated rank table or external certificate.

## Focused Proof Gate

```sh
LEAN_NUM_THREADS=4 lake build Math.Algebra.Audit.AuditJetEOMCompletion Physics.FieldTheory.Jets.Audit.AuditWeylJetAdjoint
```

Passed: 3288 jobs, 38 mathematical and 72 physical public declarations,
110 strict transitive axiom checks. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. The new named public declarations are all explicitly
listed in the persistent audits; private reconstruction helpers are reached
through their proved public interfaces.

Focused checks also built the kernel, generic single-field theorem, jet
conjugation, exterior adjoint, actual Weyl null consumer, right equations and
paired adjoint. Intermediate elaboration failures were repaired without
changing the mathematical hypotheses or resource limits. In particular,
dependent membership transport was replaced by explicit short helper lemmas
and named subtype/module instances to stay within default heartbeats.

## Final Gate

```sh
LEAN_NUM_THREADS=4 lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
git diff --check
```

The full build passed: 7637 jobs. Layout passed for 2143 modules, including
layers, local imports, cycles, aggregate coverage and relocation audits.
Local links passed for 1142 Markdown files and 125 heading fragments, with no
errors. The unchanged link checker ran where its read-only Git subprocess is
permitted. The final topic/outcome index and portable metadata checks passed;
the final diff is whitespace-clean.

All 110 named public declarations were cross-checked against the two explicit
audit lists. New implementation sources contain no `sorry`, custom axiom or
resource-limit override. The new residual warnings only recommend adopting
the Lean module system for imports; existing project warnings remain. Root
README, Lean and dependency pins are unchanged.

The statements, source/dual conventions, source register, mathematical and
physical proof dossiers and assumptions ledgers were reviewed together. The
literature list is reconciled before any later integration. No paper-wide,
amplitude, interacting-field or general EFT counting claim is introduced.
The final edits after the proof gate are documentation only; no further Lean
build was run for those edits. That original proof stop was unmerged; the
subsequent integration is recorded below.

## Integration Into The Linear-EOM/Weyl Parent

The child was merged into its recorded `proof/linear-eom-weyl` parent with
`git merge --no-ff proof/jet-eom-completion`. Both worktree and target were
clean, and the target had no independent advance. The resulting Lean sources
and dependency pins equal the verified child tree; no semantic conflict arose.

The merged state passes the four-audit focused command covering
`AuditLinearJetEquation`, `AuditWeylLinearEquation`, `AuditJetEOMCompletion`
and `AuditWeylJetAdjoint`: 3424 jobs and 255 strict transitive checks
(94 + 51 + 38 + 72). Full `LEAN_NUM_THREADS=4 lake build` passes 7637 jobs
under the same timeout, thread and address-space guard. Layout passes for
2143 modules; documentation links, topic/outcome coverage, portable metadata
and diff checks pass. Existing warnings and the standard-axiom policy remain.

The source register is reconciled into `RELATED_LITERATURE.md`. Integration
records change documentation only after the merged proof gate; no extra Lean
build is run for those edits. The historical child branch name is retained in
this record; local branch cleanup was completed after the final parent gate.

The combined `proof/linear-eom-weyl` branch was subsequently merged with
preserved history into `proof/derivative-ibp`. The final parent passes the
nine-audit 3444-job closure (625 strict checks), the 7637-job full build and
structural/documentation gates. The
[parent integration record](../derivative-ibp/verification.md) owns this final
gate. No master merge or remote update is performed.

The local child branch was deleted with `git branch -d` after confirming its
HEAD reachable from the recorded parent and the final derivative/IBP target,
no worktree using it, and no pending child work requiring it. Its historical
name and integration target remain in this record.
