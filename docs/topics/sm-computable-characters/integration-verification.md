# Master integration verification

The user explicitly requested the master merge after the root README update.

- Original master/base: `checkpoint 01`.
- Final topic head: `checkpoint 02`, on `proof/sm-computable-characters`.
- Integrated 44 topic commits using
  `git merge --no-ff proof/sm-computable-characters`.
- Merge commit: **`checkpoint 03`**, with parents `checkpoint 01` and `checkpoint 02`.
- No conflicts. The merge tree equals the final topic tree:
  a Git tree comparison between the recorded checkpoints passed.

## Merged-state checks

Strict audits were executed afresh with `lake env lean` through the existing
guarded runner, not merely replayed from cached audit output. The runner
used one Lean thread, a 6 GiB sampled process-group RSS cap, 4 GiB host reserve
and 90 s wall cap.

- Math structural audit: **2018 transitive declarations**, success;
  guarded 5.0 s, sampled peak 5322420 KiB.
- Physics structural audit: **346 transitive declarations**, success;
  guarded 3.8 s, sampled peak 5425100 KiB.
- Total: **2364 strict checks**, admitting only `propext`, `Classical.choice`
  and `Quot.sound`.
- Default **`lake build`**, including **GUT**, succeeded for **7320 jobs**
  using cached targets, zero warnings/errors. The serialized runner used a
  10 GiB process-group cap, 4 GiB host reserve and 300 s wall cap; guarded
  3.3 s, sampled peak 891868 KiB, `stopped=False`.
- `node tools/layout/check-layout.mjs`: **1934 modules**, layer/import,
  cycle, aggregate and relocation checks pass.
- `python3 tools/exact-rank/check-retired-certificates.py`: **19 snapshot
  hashes verified, 15 retired numerical modules absent from active imports**.
  No retired numerical proof was built.
- `python3 tools/exact-rank/test-kernel-probe.py`: **8 tests pass**.
- Local documentation links and `git diff --check` pass, including the
  final documentation-only integration record. No theorem or dependency
  file was changed after merged-state proof verification.

Build/probe output remains in `/tmp`; no disposable output was committed.
The root README update is included in the merge. The final support theorem
and the separate conditional character route retain their documented scopes;
see [full support results](full-support-results.md).

## Branch cleanup and remaining boundaries

After successful merged-state verification, reachability of the complete
topic head from master was confirmed. No worktree used the topic branch,
and no pending child branch was present. `git branch -d` then safely removed
the local topic branch. Its name and final head remain recorded above.
The unrelated detached worktree was left untouched.

No remote push, remote branch deletion or history rewrite was performed.
The only subsequent changes are this integration record and the topic
metadata; they do not establish a different proof baseline.
