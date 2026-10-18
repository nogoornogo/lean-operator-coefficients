# Portable documentation metadata

## Scope

The public snapshot must be understandable without local Git history or an
older documentation layout. Maintained Markdown and JSON evidence omit local
Git IDs, work dates and timestamps. Named milestones or document-local sequence
numbers retain necessary ordering without inventing global identifiers.

The user removed the earlier old-layout preservation exception. All retained
proof, assumption and technical verification documents now follow this rule.
External dependency/source revisions, publication dates, content checksums and
required license/attribution information remain. Metadata cleanup changes no
proof premise and does not imply that old builds have been rerun.

## Changes and checks

Removed work-history fields from structured evidence while retaining numerical
results, audit counts, commands and snapshot hashes. Updated headings, dated
filenames and incoming links. Git comparisons requiring unavailable local IDs
are described as recorded comparisons rather than fake executable commands.
AGENTS, WORKFLOW and the topic template prohibit reintroducing work metadata.

`python3 tools/docs/check-work-metadata.py` checks all maintained Markdown/JSON
files and dated document filenames. Its explicit source exceptions identify
external revisions and publication dates. It rejects mixed/numeric revision
candidates and retired metadata fields, while allowing numerical measurements.
It is a bounded text check, not a semantic detector for every possible date
format or arbitrary numerical string; citation metadata is also reviewed.

The current acceptance commands and results are recorded in the
[snapshot-only verification](snapshot-documentation-verification.md).
No old directory mapping, historical Git object or document exemption is
needed by these checks. No Lean build or axiom audit was rerun.
