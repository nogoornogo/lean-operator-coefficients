# Integration into the minimum-dimension parent

The frozen plan records a bounded child of the unmerged
`proof/sm-minimum-operator-dimension` branch. Its parent exception authorizes
integration into that parent under WORKFLOW.md; it never authorizes a master
merge or remote push.

- Plan checkpoint: `checkpoint 01`
- Verified implementation checkpoint: `checkpoint 02`
- Parent merge: `checkpoint 03`
- Historical child branch: `proof/sm-b1-below-ten`; safely deleted

The target had not advanced. The worktree list confirmed it was not checked
out elsewhere. After switching to the parent, `git merge --no-ff` completed
without conflicts. `git diff --exit-code proof/sm-b1-below-ten HEAD` confirmed
the merged tree exactly matched the verified child checkpoint.

Merged-state checks used the unchanged one-thread, 300-second, 10 GiB sampled
RSS and 4 GiB reserve guard:

| Check | Seconds | Sampled group peak KiB |
| --- | ---: | ---: |
| Direct child audit: 69 strict transitive checks | 4.5 | 5123500 |
| Direct parent minimum audit: 140 strict transitive checks | 4.3 | 5124352 |
| Full default-root `lake build GUT`: 7352 jobs | 3.3 | 914324 |

The full build was a cached replay, with zero warnings/errors; its lower
peak is not a fresh-source performance measurement. The two direct audits
were freshly executed. Layout passes 1966 modules; merged-state links and
diff checks pass. Final record-only documentation adds no Lean change and
does not require another full build.

The final record-only link check first encountered a sandbox `spawnSync git
EPERM` restriction. The unchanged read-only checker passed on its permitted
outside-sandbox retry: 1002 Markdown files, 6088 links, 115 fragments, zero
errors. No checker change or approval rejection occurred.

After successful merged verification, `git merge-base --is-ancestor`
confirmed the child HEAD was reachable from the parent, and the worktree
list showed no worktree using the child. There is no pending child work
requiring that branch as an integration target. `git branch -d` succeeded.
The unrelated untracked `docs.zip` and the other detached worktree were left
untouched. Master and remote state were not changed.
