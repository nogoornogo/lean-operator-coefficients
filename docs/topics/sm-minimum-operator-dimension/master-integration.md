# Master integration (stage 01)

The user explicitly requested merging the completed minimum-dimension topic
into master. This includes the initial four minima and the three recorded
bounded child phases, ending with all 326 finite-domain B1 minima proved.

- Master/base before merge: `checkpoint 01`
- Final topic checkpoint: `checkpoint 02`
- Topic: `proof/sm-minimum-operator-dimension` (historical; safely deleted)
- Master merge: `checkpoint 03`

The target had not advanced beyond the recorded base. Review confirmed only
the authorized topic/children and their evidence, unchanged toolchain and
dependency pins, no root README edit and no tracked dirty user work. The
unrelated untracked `docs.zip` was preserved. Worktree inspection showed no
other checkout of master. `git merge --no-ff` completed without conflicts.
An empty tree diff against the final topic checkpoint confirmed the merged
source exactly matches the verified topic tree.

## Merged-state verification

Each Lean check used one thread, 300 seconds, 10 GiB sampled process-group
RSS and a 4 GiB available-memory reserve, with unchanged proof options and
allowlists. The four audits were executed directly, rather than accepted
only as cached build output.

| Direct audit or build | Checks/jobs | Seconds | Sampled group peak KiB |
| --- | ---: | ---: | ---: |
| `AuditSMMinimumOperatorDimension` | 140 strict checks | 4.3 | 5122288 |
| `AuditSMB1BelowTen` | 69 strict checks | 4.0 | 5126068 |
| `AuditSMB1MinimumClassification` | 288 strict checks | 4.0 | 5127752 |
| `AuditSMB1ExactMinima` | 67 strict checks | 4.5 | 5130936 |
| Full default-root `lake build GUT` | 7364 jobs | 4.0 | 912684 |

The full build is cached replay, zero warnings/errors; its sampled peak is
not a fresh-source performance measurement. The connection progress probe
regenerates byte-for-byte on merged master. Layout passes 1978 modules,
local links and diff checks pass, and the accepted source hashes agree.
Final links cover 1011 Markdown files, 6127 local links and 115 fragments,
zero errors, using the unchanged read-only checker's permitted retry.
[Machine-readable evidence](master-integration.json) retains commands and
measurements. Earlier failed resource runs remain failures in their own
records, with the later verified resolution linked; no guard was raised.

## Cleanup and remaining boundary

After merged verification, `git merge-base --is-ancestor` confirmed the topic
HEAD was reachable from master. The worktree list showed no checkout of the
topic, and its bounded child branches had already been integrated/deleted;
no pending child needs the topic as a target. Normal `git branch -d` succeeded.
The other detached worktree and user files were untouched. No remote push,
remote branch deletion, history rewrite or publication occurred.

All 326 allowed rows in the existing 572-assignment B1 domain have actual
minimum certificates; 246 rows remain all-degree forbidden with no numeric
minimum. The fixed derivative-free SM/Higgs dictionary and the finite-domain
boundary remain unchanged. Other requested follow-ups were not started.
Final record-only edits change no Lean source and require link/diff checks,
not a new Lean build or proof baseline.
