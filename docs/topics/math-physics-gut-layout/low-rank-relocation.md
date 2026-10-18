# Bounded mathematics relocation and worktrees

Retained source-relocation and verification evidence from a mixed editorial/technical task.
The checks below describe that checkpoint, not a new build.

The user authorized obsolete-worktree cleanup and relocation of generic
mathematics on this existing branch. Six low-rank Lie modules were moved to
`Math/Algebra/Lie`, retaining declarations and proof bodies; imports, links,
the aggregate and relocation map were updated. A persistent axiom audit was
added. No namespace migration, premise relaxation or dependency update is in
scope. The SU(n) exponential and normalized-Laurent candidates still import
GUT bridge modules and require a separate dependency-separation step; no upward
Math imports are permitted to facilitate their move.

Both obsolete worktrees had clean tracked/untracked status and retained HEADs.
Their directories and stale Git metadata were removed; branches were retained.
The workflow now specifies dirty/ignored-data and detached-HEAD checks before
future removals. Topic-index regrouping remains a proposal, not implemented.

This source-relocation follow-up was verified separately from the earlier
documentation-only passes: the focused audit build and `lake env lean
Math/Algebra/Lie/Audit/AuditLowRankHighestWeight.lean` passed seven strict
transitive checks (only `propext`, `Classical.choice`, `Quot.sound`). Full
`lake build` passed (6,068 jobs); existing linter/deprecation warnings remain.
Layout checks passed for 1,015 modules, Markdown checks passed for 370 files and
2,496 local links, and `git diff --check` passed. The docs/layout tests passed
14/14 after rerunning outside the sandbox: the initial fixture-based docs test
failed with `spawnSync git EPERM`, not a link-validation failure.
