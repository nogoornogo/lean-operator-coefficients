# Topic Title

- ID: `<topic-id>`
- Status: planned
- Result type: not established
- Working branch: unassigned
- Integration target: unassigned
- Integration evidence: Git ancestry into the recorded target; report merge outcome

Use exactly one status value: `planned`, `in-progress`, `blocked`, `deferred`,
or `completed`. Put endpoint qualifications and integration outcomes in the
result section, not in the Status value. Do not add work dates, timestamps or
local Git IDs. Use named milestones or document-local sequence numbers when
order matters; link verification records rather than requiring old Git objects.

## Endpoint And Scope

State the exact output/consumer, assumptions, non-goals and why it is needed.

## Deliverables And Acceptance

List finite interfaces/artifacts, focused checks and the completion condition.
State the investigation bound and conditions requiring a scope decision.

## Work And Open Obligations

Record actionable remaining work and the next action or stopping decision.

## Result And Verification

Record the scoped result, limitations, commands and outcomes. Do not report an
unrun build. Link larger milestone records rather than append session narratives.

## References

Link the necessary sources, proof dossiers and verification records.

## Outcome-guide entry

After verified integration, or an explicitly settled unmerged stop/deferral,
append the topic name, relative folder link and brief outcome/stopping reason
to the last [history-guide volume](_history/README.md). No date, timestamp or
commit ID belongs in that entry. Detailed status and verification stay here.
The guide records reading order, not topic IDs or a duplicate status database.
