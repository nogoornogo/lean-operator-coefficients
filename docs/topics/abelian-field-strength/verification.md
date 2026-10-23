# Verification

Working branch: `proof/abelian-field-strength`; integration target:
`proof/derivative-ibp`, under the recorded bounded-child exception. The initial
worktree was clean. The parent remains unmerged into master. No dependency pin,
old proof, audit allowlist or root README change is included.

## Proof Gate

```sh
LEAN_NUM_THREADS=4 lake build Physics.FieldTheory.Jets.Audit.AuditMaxwellLinearEquation
```

Passed: 3280 jobs. The persistent physical audit explicitly checks 112 named
public declarations and their transitive dependencies; only `propext`,
`Classical.choice` and `Quot.sound` are permitted. It rejects GUT source imports.
All five implementation files and the audit are registered in `Physics.lean`.
The metric/tensor action, actual seed covariance, full relation quotient,
antisymmetry/diagonal and wave descendants, two independent transverse probes,
actual symmetric algebra and inverse equivariant EOM/IBP consumer are built.
The common empty-odd algebra is explicitly algebra-equivalent to the symmetric
algebra, with its generator formula proved. All named public declarations are
cross-checked against the explicit audit list; private helpers are reached
transitively through those declarations.

Heavy commands use four threads, a 540-second timeout and an inherited 16 GiB
per-process address-space guard. Default heartbeat, recursion and kernel limits
remain unchanged. One earlier focused attempt ended with the host error
`failed to create thread: Resource temporarily unavailable` (exit 134). The
next run under the same limits succeeds; no theorem or audit premise was
weakened. Disposable logs and the guard wrapper stay outside source control.

## Final Acceptance

```sh
LEAN_NUM_THREADS=4 lake build
node tools/layout/check-layout.mjs
node tools/docs/check-links.mjs
python3 tools/docs/check-topic-index.py
python3 tools/docs/check-work-metadata.py
git diff --check
```

The final full build passes 7643 jobs, including Math, Physics, GUT and all
persistent audits. It follows the final symmetric-algebra identification;
the preceding full build is not used to cover that later proof change. Layout
passes for 2149 modules, with layer/import, cycle, aggregate and relocation
gates. Documentation links pass for 1148 Markdown files and 125 heading
fragments, with zero errors. The unchanged checker runs where its read-only
Git subprocess is permitted. All 152 topics and outcomes are indexed without
pending exceptions. Portable metadata passes for 1140 files. The diff is
whitespace-clean.

The implementation sources contain no `sorry`, custom axiom or resource-limit
override. New residual warnings are module-system import recommendations;
existing project warnings remain. No dependency or root README change occurs.
The frozen equations, source/dual convention, proof dossier, source register,
bibliography and Physics assumptions ledger agree. Generic linear EOM inputs
remain explicit in the shared package; this physical consumer proves its own
covariance inputs.

The final edits after the successful proof gate are documentation only; no
further Lean build is run for those edits. The endpoint is committed on the
child branch and remains unmerged into its recorded parent. No master merge,
remote mutation or new foundational/physical topic is started at this stop.

## Parent Integration

The original child proof stop above is retained as checkpoint evidence. Under
explicit user direction, the clean child was merged into its recorded parent
with `git merge --no-ff proof/abelian-field-strength`. The target had no
independent advance and no conflict resolution was needed. The merged Lean
sources, root README and dependency pins equal the verified child tree.
The source register was already reconciled into the bibliography before merging.

The combined parent audit closure passes 3450 jobs and 737 strict transitive
checks across ten audits, including this topic's 112 checks. The full build
passes 7643 jobs; layout passes 2149 modules. The same four-thread, 540-second
and inherited 16 GiB address-space guards apply. Standard-axiom and import
policies remain unchanged; module-system recommendations and existing project
warnings remain. Final documentation gates and local branch cleanup are
recorded in the [parent verification](../derivative-ibp/verification.md).

Integration record edits after these proof checks are documentation only; no
further Lean build is run for them. The parent remains unmerged into master,
and no remote mutation or further proof topic is started.
