# Topic history guide

This append-only guide records topic outcomes and links to their canonical
folders. It does not own status, open obligations or detailed verification.
Entries contain a topic name, relative folder link and a brief outcome or
stopping reason. Do not include dates, timestamps or commit IDs.

Numbered files are reading-order volumes, not topic IDs or entry numbers.
Aim for about 25 entries per file; a coherent phase boundary can justify a
slightly different size. Append to the last volume and create the next one
when appropriate. Do not reorder earlier volumes for subject classification.

The initial backfill follows preserved record groupings and available Git
path-introduction order. It is not a reconstructed exact completion chronology.
Grouped earlier records do not imply one original topic branch or one merge.
Git preserves exact edit timing and prior versions. Maintained documentation
uses named milestones or sequence numbers instead of work dates and local Git IDs.

Append a concise outcome when a topic is merged, or when an unmerged stop or
deferral is explicitly settled. Coordinate through the integration worktree;
resolve parallel append conflicts by retaining both outcomes once. Active work
is tracked in its topic, not entered as a completed result here. The current
documentation topic receives an entry only at integration or a terminal decision.

See [WORKFLOW](../../architecture/WORKFLOW.md) and the [topic index](../README.md).

## Coverage

All settled or integrated topic folders must be linked here. The subject index
also covers active topics. Check both with
`python3 tools/docs/check-topic-index.py`; explicitly name pending topics with
`--pending-topic <topic>` while their integration or outcome is outstanding.
The initial backfill prefix is retained; later corrections append missing
outcomes without claiming an exact historical completion order.

## Volumes

- [Volume 001](001_topics_history.md).
- [Volume 002](002_topics_history.md).
- [Volume 003](003_topics_history.md).
- [Volume 004](004_topics_history.md).
- [Volume 005](005_topics_history.md).
- [Volume 006](006_topics_history.md).
- [Volume 007](007_topics_history.md).
- [Volume 008](008_topics_history.md).
- [Volume 009](009_topics_history.md).
