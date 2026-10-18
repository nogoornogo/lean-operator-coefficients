# Master integration and verification

On stage 01 the user explicitly requested merging the completed topic into
master. Topic HEAD was `checkpoint 01`;
master remained at the recorded base `checkpoint 02`.
The worktree was clean. The endpoint diff and dependency pins were reviewed;
no pin, proof-limit or audit-allowlist changes were introduced.

`git merge --no-ff proof/sm-finite-charge-support` completed without conflicts
as `checkpoint 03`. The merged tree is identical
to the topic checkpoint (a Git tree comparison between the recorded checkpoints).

## Merged-state verification

Each Lean invocation used `LEAN_NUM_THREADS=1` and
`python3 tools/exact-rank/kernel-probe.py`, with `--rss-limit-gib 10`,
`--min-available-gib 4`, `--timeout-seconds 300`. Runs were serialized.
Audits were directly elaborated from their source paths under
`Physics/StandardModel/Operators/Audit/`, rather than relying on cached
audit replay. Only propext, Classical.choice and Quot.sound are permitted.

| Check | Result | Seconds | Sampled group peak KiB |
| --- | --- | ---: | ---: |
| `AuditSMFiniteLeptonSupport.lean` | 1199 strict transitive checks | 4.5 | 5120856 |
| `AuditSMFiniteLeptonDegreeBounds.lean` | 52 strict transitive checks | 4.3 | 5123496 |
| `AuditSMChargeDegreeBounds.lean` | 13 strict transitive checks | 3.5 | 5087936 |
| `--build GUT` (`lake build GUT`) | 7345 jobs, zero warnings/errors | 3.5 | 918764 |

The full build is an up-to-date cached build, not a fresh elaboration benchmark.
`node tools/layout/check-layout.mjs` passes 1959 modules.
`node tools/docs/check-links.mjs` and `git diff --check` pass. The link checker
initially hit a sandbox Git subprocess restriction and passed unchanged when
rerun outside that restriction. The initial Git switch also required Git
metadata write access; the authorized merge then succeeded.

The earlier optional independent generated certificates were not repeated:
their verified source tree is unchanged by integration. CSV snapshots and
the optional historical comparison tools are retained at the user's direction;
CSV is not a Lean proof input. Minimum total operator dimension and UV/decay
physics remain outside scope.

## Branch lifecycle

Before deletion, `git merge-base --is-ancestor` confirmed topic HEAD reachable
from master. `git branch --contains` showed only master and the topic branch;
`git worktree list --porcelain` confirmed no worktree used the topic branch.
The bounded child topic was already complete, merged into its parent and
deleted; no pending child needed the parent. While on master, `git branch -d`
safely deleted local `proof/sm-finite-charge-support`. The unrelated detached
worktree was unchanged. No remote push or remote branch deletion occurred.

This integration record and the topic overview are documentation-only
follow-ups. Their link/diff checks do not change the Lean baseline above;
no additional Lean build is required for those record edits.
