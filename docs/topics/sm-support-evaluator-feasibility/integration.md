# Master integration

The user explicitly authorized merging the completed topic into `master`.
The clean topic tip `checkpoint 01` was merged from
master `checkpoint 02` with
`git merge --no-ff audit/sm-support-evaluator-feasibility` as
`checkpoint 03`. There were no conflicts and master
had no independent commits. a Git tree comparison confirmed
that the initial merged tree exactly matched the verified topic tree.
No unrelated branch/worktree was integrated or modified, and no push occurred.

## Merged-state verification

One serialized Lean run at a time, unchanged pins/proof options,
120-second guard, 10 GiB sampled process-group RSS and 4 GiB host reserve:

| Check | Seconds | Sampled peak KiB |
| --- | ---: | ---: |
| Default-root `lake build GUT`, 7335 jobs | 3.3 | 914364 |
| Direct compact occupation audit, 13 checks | 3.3 | 4696704 |
| Direct joint-source data audit, 56 checks | 3.5 | 5228120 |
| Direct reexpression audit, two checks | 3.5 | 5159320 |
| Direct compact Physics audit, 12 checks | 3.5 | 5380036 |
| Direct joint-data Physics audit, 34 checks | 3.5 | 5373232 |
| Fresh ordinary consumers, five strict checks | 3.8 | 5040168 |
| Runtime degree-6 metadata diagnostic | 3.3 | 5027268 |
| Runtime degree-13 metadata diagnostic | 3.5 | 5036384 |

The full build is cached because the merged source tree is unchanged from the
topic. All five added audit files were separately executed from source,
**117 strict transitive checks** in total, plus five freshly elaborated ordinary
consumer proofs. No warnings/errors or guard interruptions occurred. The
largest sampled peak in this merged-state verification is about 5.13 GiB.
Runtime diagnostics print the same signed-core counts and balanced Q18 count
8000; printed values are not proof premises.

Commands use `tools/exact-rank/kernel-probe.py` with `--rss-limit-gib 10
--min-available-gib 4 --timeout-seconds 120`, `--build GUT` for the root and
individual added audit paths for direct audits. Fresh diagnostic files are
copied from `sm-joint-data-consumers.lean.txt` and `sm-joint-data-use.lean.txt`
in `tools/structural-support/probes/`; runtime input is `SM_DATA_DEGREE=6/13`.
Disposable logs are under `/tmp/sm-support-merged-*`.

Existing 107/572 numerical certificate proofs were not rerun or made premises
of the new ordinary connection proofs. Exact regeneration of both historical
Lean certificate files agrees with their accepted SHA256 values; the 572-row
output and recorded input/source hashes also match byte-for-byte. This checks
preservation of prior evidence, without introducing computational support
proofs into this merge verification.

Repository checks: layout passes for 1949 modules; retired-certificate check
passes 19 snapshot hashes and absence of 15 retired modules; local links and
diff checks pass (981 Markdown files, 5995 local links, 113 fragments, zero
link errors). The initial retired-check invocation used a nonexistent
layout-script path; the retained check was run successfully at its actual path,
`python3 tools/exact-rank/check-retired-certificates.py`. No checker changed.
The integration-record update is documentation-only and does not create a
new proof baseline or require another Lean build.

## Local branch cleanup and retained boundary

The topic tip is reachable from master, no worktree uses the topic branch,
and no other local branch contains that tip as pending child work. The
unrelated detached worktree is retained.
`git branch -d audit/sm-support-evaluator-feasibility` succeeded after merged-state
verification, deleting the local branch at `checkpoint 04`. No force deletion, remote deletion,
remote push or shared-history rewrite is authorized.

The verified data connection and named consumers remain distinct from a
general compiled support solver or a universal resource guarantee for witness
search. Phase records retain their earlier checkpoint-specific failures,
resource measurements and pre-merge state. This integration record owns the
current integration result.
