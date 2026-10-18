# Documentation Separation And Master Integration

The user authorized the new documentation layout and master integration on
stage 01. Reader-facing applications live under `docs/model-studies/`; the
SU(6) plans, stopping decision and checkpoint records remain under `docs/topics/`.
The attempted historical relocation was corrected before committing.

This restructuring changes no Lean source or dependency pin. The integration
also includes the topic's previously verified proof checkpoints, so focused
builds, strict transitive audit execution and a full build are checked separately
from documentation acceptance. Integration results are recorded below.

## Checks

Pre-merge verification at stage 01:

- Focused `lake build` of all 21 audit modules added relative to master:
  passed, 4,135 jobs.
- `lake env lean <audit-file>` executed serially for each of those 21 files:
  193 strict transitive checks passed. Only `propext`, `Classical.choice` and
  `Quot.sound` are admitted; no audit exception was added.
- Serialized `lake build`: passed, 6,591 jobs, no warnings.
- `node tools/layout/check-layout.mjs`: 1,264 modules passed.
- `node tools/docs/check-links.mjs`: 530 Markdown files, zero errors.
- `python3 tools/su6-twisted-protection/audit_nonlift.py`: six tests passed.
- `python3 tools/su6-twisted-protection/audit_block_phase.py`: six tests passed.
- `python3 tools/qque/audit_one_generation.py`: four tests passed.
- `git diff --check` and staged diff review: passed. Dependency pins unchanged.

The documentation edit does not require a new proof baseline; the build and
strict audit reruns above verify the proof-containing integration separately.
The integration target had not advanced beyond the recorded base.

## Integration

Documentation checkpoint: `checkpoint 01`.
User-authorized `git merge --no-ff proof/su6-twisted-protection` succeeded without
conflicts; merge commit: `checkpoint 02`.

Merged-state verification on master:

- The merge tree exactly matched the verified topic tree (`git diff` exit zero).
- `lake build`: passed, 6,591 jobs. This reuses the unchanged audit modules;
  the 21 direct audit executions above remain the fresh strict audit evidence.
- Link check: 530 Markdown files, zero errors; layout check: 1,264 modules passed.
- All three exact Python audits rerun: 6 + 6 + 4 tests passed.
- `git diff --check`: passed.

The topic HEAD was confirmed reachable from master, no worktree used the topic
branch and no child branch depended on it. Local branch deletion with
`git branch -d proof/su6-twisted-protection` succeeded. Branch names and earlier
checkpoint evidence remain in the topic record. No remote push was performed.
The final verification-record update is documentation only; links and whitespace
are checked again, without a further Lean build.
