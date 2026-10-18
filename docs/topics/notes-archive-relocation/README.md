# Remaining Notes Archive Relocation

- ID: notes-archive-relocation
- Status: completed
- Result type: documentation maintenance
- Working branch: `docs/notes-archive-relocation`
- Integration target: `master`

## Endpoint And Scope

Move the eight remaining files under `notes/archive/e6-leanstral/` to
`docs/history/e6-leanstral/`, following the user-approved documentation layout.
Update current references and relative links, preserving rejected-draft warnings
and historical claims as historical evidence, not accepted mathematics.

Keep the six `.lean.txt` drafts byte-identical and excluded from the Lean build.
The old status report changes only in link destinations. No proof, assumption,
dependency pin or literature-input boundary changes. Historical references to
former paths in earlier milestones are not instructions to recreate `notes/`.

## Acceptance

- Compare all six draft files and the status report with the base version,
  allowing only the three relative-link corrections in the status report.
- Check that the only Lean source change is a documentation path.
- Run `node tools/docs/check-links.mjs` and `git diff --check`.
- No Lean build is rerun for this documentation-only change.
- Commit and merge into `master`; retain the topic branch.

## Result And Verification

- All eight files now reside in the [historical archive](../e6-global-topology/drafts/README.md).
  The empty `notes/archive/` and `notes/` directories were removed.
- Byte comparisons passed for all six drafts. The archived status differs
  only in the three link destinations. The one Lean-source edit changes only
  the archive path in its module comment.
- `node tools/docs/check-links.mjs`: 212 Markdown files, 1114 local links,
  32 heading fragments, zero errors.
- `git diff HEAD --check`: passed. No Lean build was rerun; the existing
  proof verification baseline and literature boundary are unchanged.
- No remaining work in this topic. Git ancestry records integration into
  `master`; the work branch is retained.
