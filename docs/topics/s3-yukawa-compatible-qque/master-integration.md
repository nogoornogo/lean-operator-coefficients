# Master integration

The user authorized the reader-facing model-study addition and master merge
at stage 01. The proof checkpoint is checkpoint 01; the branch base and unchanged
master target before integration are checkpoint 02.
The source endpoint and its [verification](verification.md) remain unchanged.

The [model study](../../model-studies/s3-flavor-qque/README.md) supplies the
reader-facing fixed input, outcome and limits. The topic retains operational
records and the existing proof dossier retains theorem details. No root README
change is included. The addition is documentation-only: local link and diff
checks apply; no Lean build was rerun for this documentation checkpoint.

## Integration result

The documentation checkpoint is checkpoint 03. Merge checkpoint 04 integrated the topic
with `git merge --no-ff proof/s3-yukawa-compatible-qque`, without conflicts.

Merged-state verification passed:

- Guarded full `lake build GUT` (the default target): 7,366 jobs, exit 0,
  3.3 seconds, sampled group peak 915,304 KiB. The same one-thread, 300-second,
  10 GiB sampled RSS and 4 GiB host-reserve guards were retained.
- The persistent 25-declaration strict transitive audit passed on replay;
  no warnings or errors were reported.
- Exact supplementary check: 486 invariant and 81 symmetry cases, witness 1,
  missing-sign negative control -1, all passed.
- Layout: 1,980 modules passed. Links: 1,016 Markdown files, 6,150 local links,
  116 heading fragments, zero errors. `git diff --check` passed.

Ancestry confirmed topic HEAD checkpoint 03 is reachable from master. No worktree
uses the topic branch and no child work needs it; normal `git branch -d`
succeeded after switching to master. Unrelated docs.zip and the detached
worktree were untouched. No push or remote branch deletion occurred.

The final integration-record edits are documentation-only; link/diff checks
were rerun, without another Lean rebuild.
