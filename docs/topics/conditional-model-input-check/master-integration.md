# Master integration

The user authorized integration after accepting the bounded model-checking pass
as complete. Topic head checkpoint 01 (preceded by checkpoint 02 and checkpoint 03) was merged
with `git merge --no-ff proof/conditional-model-input-check` into unchanged
master base checkpoint 04. Merge commit: checkpoint 05. No conflict occurred.

## Merged-state verification

The guarded full default-target `lake build GUT` passed: 7,374 jobs, exit 0,
3.6 seconds, sampled group peak 915,952 KiB. One Lean thread, 300 seconds,
10 GiB sampled group RSS and 4 GiB host reserve were unchanged. The persistent
43-, 48- and 12-declaration strict transitive audits all passed on replay;
there were no warnings or errors. Disposable log:
`/tmp/conditional-model-merged-full.log`.

The following merged-state supplementary checks passed:

- `python3 tools/conditional-model-input-check/check_inputs.py`.
- `python3 tools/proton-protection-model-checks/audit_models.py`: 7 tests.
- `python3 tools/species-surplus-model-checks/audit_models.py`: 5 tests.
- `python3 tools/s3-yukawa-compatible-qque/check_sample.py`: 486 invariant
  and 81 symmetry cases plus positive/negative controls.
- `python3 tools/su6-twisted-protection/check_s3_qque_tensor.py`: 3 tests.
- `python3 tools/su6-twisted-protection/audit_block_phase.py`: 6 tests.
- Layout: 1,988 modules passed. Local links and `git diff --check` passed;
  link/diff checks were repeated after this record-only update.

## Cleanup and scope

Ancestry verified that topic HEAD is reachable from master. No worktree uses
the topic branch and no child branch needs it. Normal `git branch -d` succeeded
after switching to master. The unrelated detached worktree and user docs.zip
were preserved. No remote push or remote branch deletion was performed.

The scope remains the ten-candidate conditional review, explicit B-L action
restriction and conditional LR light-Higgs identification. The source-level
LR scalar-selection premise and exact UV fermion mass radicals remain
unverified as documented in the per-model admission record. Integration does
not change these boundaries. Documentation-procedure work is a separate topic.
Final integration-record changes are documentation-only; no additional Lean
build is needed after the verified merged-state build above.
