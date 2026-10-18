# Snapshot-only documentation verification

## Authorized endpoint

The user approved removing old-layout correspondence/preservation machinery
and documents whose only purpose was explaining the former organization.
Keep substantive proofs, assumptions, verification evidence and failed-route
boundaries. Remove work dates and local Git IDs from those records too.
The earlier preservation exception and instruction to retain its checker are
superseded. No Lean proof, dependency pin, Git history or user-owned docs.zip
is changed. No master merge or remote publication is authorized.

## Implementation

- Deleted the directory correspondence table, initial backfill inventory and
  original-content preservation checker. Current checks use the latest tree.
- Removed old root/topic index copies, Git rewrite history/ID map and the
  obsolete status-layout checkpoint. Their useful navigation is already in
  current proof/topic indexes.
- Kept the semantic dependency graph, assumption-relaxation table, interface
  and coefficient checkpoints, research trajectory and technical evidence.
  These explain mathematical scope rather than old document placement.
- Renamed 41 dated or structure-specific documents and updated incoming links.
  Technical review numbering remains; dates do not determine current paths.
- Removed the work metadata exception and applied cleanup to all retained
  records. Dependency/source revisions, publication dates, checksums and
  required attribution metadata remain.
- Removed the namespace-documentation updater's correspondence-table dependency.
  It still preserves technical checkpoint declarations, selecting work records
  and explicitly scoped checkpoint dossiers by their current role.
- Moved current guide-format/volume-order validation into the ongoing topic
  index checker. No frozen backfill prefix or previous Git tree is required.
- Updated policy, templates and topic guides to describe one current structure
  and the applicable metadata rules. No mathematical result is promoted by
  deleting its old navigation or metadata.

## Checks

```sh
python3 tools/docs/check-work-metadata.py
python3 tools/docs/check-topic-index.py --pending-topic proof-scope-and-application-guide
python3 tools/docs/test-portable-doc-checks.py
node --check tools/layout/update-namespace-docs.mjs
node tools/docs/check-links.mjs
node --test tools/docs/test-check-links.mjs
git diff --check
```

Metadata checks pass for 1,039 maintained Markdown/JSON files. There are no
document-level work-history exemptions. Topic coverage remains 143 topic folders and 142
outcome-linked topics; the only pending integration is this branch's topic.
Seven persistent Python regression tests cover a snapshot with neither Git
history nor a migration inventory, source metadata, formerly exempt checkpoint
records, local revision/base-field rejection, dated filenames, missing links,
and guide format/order errors.

An isolated namespace-updater fixture confirms that it runs without the old
correspondence table, updates a current declaration reference and preserves
both topic records and explicitly scoped checkpoint text. The mutating updater
was not run on repository documents. Syntax and diff checks pass. Local links pass for 1,047 Markdown files,
6,542 local inline links and 102 heading fragments, with zero errors.
All five existing link-check regression tests pass using Git-backed temporary
fixtures; they need no earlier repository commits. A scoped comparison of
204 retained Markdown records also confirms that their four displayed-math
or Lean/math/LaTeX fenced blocks are unchanged; this is a text check, not
independent verification of the surrounding prose or a proof build.

No Lean build or axiom audit was rerun: these are documentation/maintenance
changes. Retained build and audit counts describe their original checkpoints,
not a new proof baseline. No merge, push or public-repository copy was performed.
