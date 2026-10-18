# Verified integration into the unmerged parent

This child uses the parent exception recorded in the frozen plan. It
integrates only into `proof/sm-minimum-operator-dimension`, never master.

- Plan: `checkpoint 01`
- Verified result: `checkpoint 02` (full identity in Git history)
- Parent merge: `checkpoint 03`
- Historical child: `proof/sm-b1-weak-connection`; safely deleted

The parent had not advanced. The worktree list showed no other checkout
of the parent. After committing the verified child and switching to the
parent, `git merge --no-ff` completed without conflicts. A tree diff against
the child checkpoint was empty. Unrelated `docs.zip` was preserved.

Merged-state checks kept one thread, 300 seconds, 10 GiB sampled group
RSS, 4 GiB available-memory reserve and unchanged pins/options:

| Check | Seconds | Sampled group peak KiB |
| --- | ---: | ---: |
| Fresh direct exact-minimum audit: 67 strict transitive checks | 4.3 | 5130916 |
| Full cached `lake build GUT`: 7364 jobs, zero warnings/errors | 3.3 | 916468 |

The full build is cached replay and does not measure fresh source checking.
The strict audit was executed directly again. Layout passes 1978 modules;
diff checks pass. Final record-only link/evidence updates change no Lean
source and require no further full build.
Final links pass 1010 Markdown files, 6125 local links and 115 fragments,
zero errors, using the unchanged read-only checker's permitted retry.

After successful merged verification, ancestry confirmed the child HEAD is
reachable from the parent, the worktree list showed no checkout of the
child and no pending child needs that ref. Normal `git branch -d` succeeded.
The other detached worktree was untouched. Master, remotes and unrelated
user files were not changed. No push or publication occurred.
