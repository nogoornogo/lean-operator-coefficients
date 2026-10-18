# Retained partial-result integration

The frozen plan authorizes bounded integration into the unmerged
`proof/sm-minimum-operator-dimension` parent under the recorded parent
exception. The full 326-minimum objective remains unachieved; integration
accepts only the verified partial result and resource-stop record.

- Plan: `checkpoint 01`
- Partial checkpoint: `checkpoint 02`
- Parent before integration: `checkpoint 03`
- Parent merge: `checkpoint 04`
- Historical child: `proof/sm-b1-minimum-classification`; safely deleted

The parent had not advanced. Worktree inspection showed no other checkout
of either relevant branch. The committed child had no tracked dirty work;
the unrelated untracked `docs.zip` was preserved. `git merge --no-ff`
completed without conflicts, and `git diff --exit-code` against the child
confirmed the exact same merged tree as the verified partial checkpoint.

Merged-state verification retained one thread, 300 seconds, 10 GiB sampled
group RSS and 4 GiB reserve:

| Check | Seconds | Sampled group peak KiB |
| --- | ---: | ---: |
| Fresh direct retained audit: 288 strict transitive checks | 4.3 | 5128004 |
| Full cached `lake build GUT`: 7358 jobs, zero warnings/errors | 3.3 | 917948 |

The full build is cached replay; its peak is not a new-source performance
measurement. Layout passes 1972 modules and diff checks pass. Final
documentation-only link checks and evidence updates do not change Lean
sources or require another full build. The stopped weak source was not
retried, and no accepted interface uses its proposed inequality.
Final links pass 1007 Markdown files, 6108 local links and 115 fragments,
zero errors, using the unchanged read-only checker's permitted retry.

After successful merged checks, `git merge-base --is-ancestor` confirmed the
child HEAD was reachable from the parent, and the worktree list confirmed
no checkout of the child. No pending child work needs that branch as a
target. Normal `git branch -d` succeeded. The other detached worktree was
untouched. Master, remotes and the user's unrelated files were not changed.
