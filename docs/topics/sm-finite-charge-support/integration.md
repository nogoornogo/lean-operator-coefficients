# Child integration and final parent verification

The user authorized a new topic branch and autonomous implementation on
stage 01. Initial plan commit: `checkpoint 01`. Stage 1 proof/tool checkpoint:
`checkpoint 02`. The bounded stage 2 child froze its contract at `checkpoint 03` and
completed its proof package at `checkpoint 04`.

The child `proof/sm-attainable-lepton-charges` was merged with `--no-ff` into
its recorded unmerged parent `proof/sm-finite-charge-support` as
`checkpoint 05`. This uses only the recorded
non-master parent exception. The parent had not advanced beyond `checkpoint 02`;
there were no conflicts. The merged tree is byte-identical to `checkpoint 04`
(a Git tree comparison between the recorded checkpoints passes).

On the merged parent, the guarded full default-root `lake build GUT` passes
all 7342 jobs, zero warnings/errors, 3.3 s, 912784 KiB sampled group peak.
This is an up-to-date cached build; it is not a fresh elaboration benchmark.
A direct fresh Lean invocation of `AuditSMFiniteLeptonSupport.lean` also
passes all 1154 strict transitive checks, 4.8 s, 5121244 KiB. Both use one
thread, 300 seconds, 10 GiB sampled RSS and 4 GiB host reserve.

The [child evidence](../sm-attainable-lepton-charges/verification.json)
records the source builds and independent cross-check on the identical
pre-merge tree: original 3724 checks, 796 degree bounds/2812 checks, exact
CSV/renderer agreement. Those long certificates were not redundantly rerun
after the byte-identical merge. Layout, links and diff checks pass. Final
record-only edits do not change the Lean verification baseline and require
no additional Lean build.

Before branch cleanup, `git merge-base --is-ancestor` confirmed the child
HEAD was retained by the parent; `git branch --contains` showed only child
and parent, with no pending child branch. `git worktree list --porcelain`
confirmed no worktree used the child. While on the parent, `git branch -d`
safely deleted the local child. Its historical name and commits remain in
the topic records. The unrelated detached worktree was not changed.

Both proof stages are complete. The working branch remains
`proof/sm-finite-charge-support`, with integration target master still
**unmerged**. No master merge, push, remote branch deletion, root README edit,
dependency/proof-limit change or publication was performed.
