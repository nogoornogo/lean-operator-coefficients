# Verification

- Working branch: `proof/sm-compact-kernel-completion`.
- Integration target: `proof/sm-statistical-finite-kernel`.
- Topic commit: `checkpoint 01`.
- Parent merge commit: `checkpoint 02`.
- The local child branch was deleted after reachability and worktree checks.
- No master merge or remote push is authorized.

## Focused proof checks

The final focused acceptance command is:

    lake build Math.LieGroups.SpecialUnitary.Audit.AuditCompactCircleTests Physics.StandardModel.Operators.Audit.AuditSMCompactFiniteKernel

The Math audit checks its dependency layer and 24 declarations. The Physics
audit checks its layer and 23 declarations. Both collect transitive axioms and
allow only `propext`, `Classical.choice` and `Quot.sound`.

Targeted builds also check `SMIntegralLocalWeights`, `SMFullLocalKernel` and
`SMQLFullKernel` directly. The final serialized full build, layout, local-link
and diff checks are recorded below after execution.

## Statement and scope review

The exact finite tests are actual elements of SU(3), SU(2), the hypercharge
circle and paired Weyl SL(2,C). Compact exhaustiveness follows from explicit
factorizations plus integral weight spanning; it does not use continuity,
density or an unproved compact/complexified invariant correspondence. The
source proof descends through the actual statistical image. The q/l theorem
retains the original charge condition and replaces each local `Allowed` term
by the explicit finite matrix-rank predicate.

No `sorry`, custom axiom, allowlist exception, dependency/pin/resource change,
root README edit or rank enumeration is included.

## Final acceptance results

- Focused audit build passed (4139 jobs): 24 Math and 23 Physics strict
  transitive checks, with both dependency-layer checks.
- One serialized `lake build` passed (6880 jobs), including the Math, Physics
  and GUT aggregates. Disposable log:
  `/tmp/sm-compact-kernel-completion-full-build.log`; no warning or error lines.
- `node tools/layout/check-layout.mjs`: 1537 modules; layers, local imports,
  cycles, aggregate coverage and relocation audits passed.
- `node tools/docs/check-links.mjs`: 813 Markdown files, 5020 local inline
  links, 94 heading fragments, zero errors.
- `git diff --check` passed.

The bounded child was merged with `--no-ff` into its recorded non-master
parent. The focused audits and serialized 6880-job full build passed again in
the merged state; the merged-state disposable log is
`/tmp/sm-compact-kernel-completion-merged-build.log` and contains no warning
or error lines. Layout, link and merge-diff checks also passed after integration.
