# Documentation verification

Checked at stage 01 on docs/proof-scope-and-application-guide, based on
checkpoint 01. This is a documentation-only change; **no Lean build or axiom audit
was rerun** and no new proof baseline is asserted.

## Editorial evidence and changes

The user's supplied ChatGPT review concerned documentation and reported an
arithmetic cross-check; the supplied Claude review reported builds and source
inspection. Their reported checks remain reviewer reports. This task read the
current IsMinimum definition and below-ten iff source for statement scope,
and the current degree dossier and model-admission records for navigation.
Source reading does not constitute a fresh proof build or independent
literature verification.

- Root README retains the three selected general results, updates stale minimum
  wording, and adds a separately scoped fixed-input/model application summary.
- The current-result map distinguishes arbitrary-modulus support/below-ten
  statements, generic minimum interfaces and the 572-row exact-minimum theorem.
- Minimum claims beside model/coverage tables now specify derivative-free
  coefficients. No derivative/EOM/IBP minimum or lifetime is claimed.
- The application guide distinguishes subgroup prohibition/permission,
  coefficient allowance/generation and proved bridges/satisfied model premises.
- Ma wording retains SM external fields and excludes N/eta external fields.
- Earlier partial proof records and stopped source evidence remain in place.
  The four-example module is distinguished from the later complete finite result.
- All-k optimization is recorded as deferred. Existing 18-charge witnesses
  prevent treating the reviewer's proposal for new witnesses as an established
  missing prerequisite without first comparing their attained grades.

## Acceptance

`node tools/docs/check-links.mjs`: pass; 1,036 Markdown files, 6,282 local
inline links, 124 heading fragments and zero errors. `git diff --check`: pass.
Review `git diff --name-only` and new files: only Markdown documentation is
changed. No Lean source, aggregate, dependency pin, test or user docs.zip is
modified. No merge or push is authorized. Build output and ZIP archives are
not added.

## Follow-up: complementary model and source views

At the user's request, both directory READMEs now distinguish model-centered
explanation from source-location-to-result indexing. Examples cover literature
B-L, project-constructed S3 and Li basis comparisons. A result can occur in
both views with cross-links; a constructed example without a specific external
comparison does not require a coverage row. The model-study listing remains
intact and is grouped under its own heading.

Local link check: 1,036 Markdown files, 6,291 local links, 124 heading fragments,
zero errors. `git diff --check` passed. This follow-up changes documentation
only; no Lean build or axiom audit was rerun.

## Follow-up: current Lean tooling guidance

Removed the obsolete MCP-specific policy/history sections and historical trial
link from LEAN_TOOLING.md at the user's request. Kept source/CLI inspection,
generated-documentation guidance and the applicable environment precautions.
Other instruction files and editor settings were not changed. The separately
discussed history restructuring and PROOF_DEPENDENCIES relocation remain deferred.

Local links: 1,036 Markdown files, 6,290 links, 124 fragments, zero errors.
`git diff --check` passed. Documentation only; no Lean build was rerun.
