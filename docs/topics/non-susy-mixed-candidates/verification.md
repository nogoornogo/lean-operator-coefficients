# Verification

Verified on `proof/non-susy-mixed-candidates`, against parent base `checkpoint 01`.

- Focused builds: `lake build Physics.StandardModel.Operators.MaZ3Mixed`,
  `lake build Physics.StandardModel.Operators.DevMohapatraSixQuark`, and
  `lake build Physics.StandardModel.Operators.Audit.AuditNonSusyMixedCandidates`
  passed. The strict transitive audit checks 53 named declarations, accepting
  only `propext`, `Classical.choice`, and `Quot.sound`. It also rejects GUT-layer
  module imports, using original-module normalization.
- Serialized `lake build` passed (6700 jobs), including a final rerun after
  correcting the audit origin diagnostic. No warnings were emitted in that
  final build. No Lean/dependency pins or audit exceptions changed.
- `node tools/layout/check-layout.mjs` passed: 1373 modules, aggregate coverage,
  layers, cycles and relocation audits.
- `node tools/docs/check-links.mjs` passed: 675 Markdown files, 4156 local
  inline links, 91 heading fragments, zero errors. The initial sandbox run
  failed to spawn git (EPERM); the unchanged checker passed with escalation.
- `git diff --check` passed. Source review found no `sorry` or custom axiom.
  Statements, domain boundaries, dossier and coverage ledger agree.

Intermediate six-quark elaboration failed on an underspecified flavor
projection and an unreduced nonzero-coordinate argument. Explicit projection
types and coordinate-equivalence unfolding resolved both; these failed
attempts are not proof premises. The parity helper's unnecessary `simpa`
lint was removed. The layout check required the audit's original-module
normalization diagnostic, which was added without weakening the check.

No generated matching, full flavored SM six-quark transport, complete-model
or phenomenological verification was performed. The untracked user `docs.zip`
and other worktree were preserved. No master merge or remote push was made.

## Master Integration (stage 01)

The child was merged into the parent at `checkpoint 02`, then the parent into
master at `checkpoint 03`, with explicit user authorization and `--no-ff`.
Merged-state `lake build` passed (6700 jobs), including the 14-declaration
DGT/quarticity and 53-declaration non-SUSY strict transitive audits.
Layout inspection passed (1373 modules); local links and `git diff --check`
passed. The subsequent integration-record edits are documentation-only;
no additional Lean rebuild is required for those edits. Git identity was
missing on the first merge attempt; command-local identity completed the
merges without repository/global configuration changes. No conflicts,
remote push or changes to the untracked `docs.zip` or other worktree.
