# CLFV Integration

On stage 01 the user explicitly requested integration. The previous
hold-on-merge instruction is superseded for this CLFV topic chain only.
No unrelated topic work was integrated, and no remote push was performed.

## Merge Chain

Each child was merged into its recorded target using `git merge --no-ff`:

| Child | Target | Merge |
| --- | --- | --- |
| proof/clfv-dipole-polynomial-automation | proof/clfv-dipole-model-interface | checkpoint 01 |
| proof/clfv-dipole-model-interface | proof/clfv-dipole-coupling-model | checkpoint 02 |
| proof/clfv-dipole-coupling-model | proof/clfv-dipole-polynomial-inputs | checkpoint 03 |
| proof/clfv-dipole-polynomial-inputs | proof/clfv-dipole-input-structure | checkpoint 04 |
| proof/clfv-dipole-input-structure | proof/clfv-dipole-completeness | checkpoint 05 |
| proof/clfv-dipole-completeness | master | checkpoint 06 |

The integration target `master` was still at the recorded base checkpoint 07.
Before this record update, `git diff --exit-code
proof/clfv-dipole-polynomial-automation HEAD` passed: the integrated tree
exactly matched the verified final topic tree. All six topic branches are
retained. The worktree was clean before switching or merging.

## Merged Verification

- `lake build`: passed, 5928 jobs; existing warnings replayed.
- Direct `lake env lean Physics/StandardModel/Operators/Audit/<file>.lean`
  checks passed for AuditDipoleCompleteness (50), AuditDipoleMediatorPaths (23),
  AuditDipolePolynomialInputs (16), AuditDipoleCouplingModel (20),
  AuditDipoleModelInterface (30), and AuditDipolePolynomialAutomation (18):
  157 strict transitive axiom checks, with model-layer import guards unchanged.
- `node tools/layout/check-layout.mjs`: passed, 875 modules.
- `node tools/docs/check-links.mjs`: passed before the record update, 328
  Markdown files, 2010 local inline links, 33 heading fragments; zero errors.
  After the documentation-only update: passed, 329 Markdown files, 2016
  local inline links, 33 heading fragments; zero errors.
- `git diff --check` and staged diff check: passed.
- No proof, dependency pins or audit allowlists were changed during integration.
  No numerical/model tests were rerun because their definitions and inputs
  were unchanged. Matching and physical decay interpretation remain subject
  to the documented model-author and scope obligations.

The final update is documentation-only; it does not rerun Lean or establish
a different proof baseline. Historical unmerged statements in milestone
dossiers describe their checkpoints; this record supersedes their integration
status only. Broader document consistency review is deferred at the user's request.
