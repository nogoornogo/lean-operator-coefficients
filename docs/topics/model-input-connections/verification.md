# Verification

The completed topic is integrated into `docs/publish-v1-upgrade`.
[Parent integration verification](integration-verification.md) records the
direct merged-state audits, full build and repository gates.

The [implementation acceptance](implementation-verification.md) records the
new proof/audit/build checks and fresh-source resource measurements. The
planning milestone below is retained as evidence of the original frozen
contract; it does not describe the present implementation status.

The later [README map follow-up](readme-verification.md) exposes the optional
field-construction routes and records diagram rendering and link checks.
It is documentation-only and does not rerun or replace the proof checks.

## What Exists

The branch records a finite implementation contract, stage estimates,
source/ownership map, model-validation matrix and stop conditions. Its
predecessor was integrated into the recorded parent before this branch was
created; see [merged-state evidence](../su6-protection-feasibility/integration-verification.md).

No new Lean declarations, implementation audits or dependency changes are
part of this milestone. No Lean build was rerun for this documentation-only
plan. The predecessor's merged-state build and direct audits verify that
integration only; they do not prove the planned shared constructions.

## Planning Acceptance

The documentation checks pass:

| Command | Result |
| --- | --- |
| `node tools/docs/check-links.mjs` | PASS; no broken local links or anchors |
| `python3 tools/docs/check-work-metadata.py` | PASS; portable records and source metadata |
| `python3 tools/docs/check-topic-index.py --pending-topic model-input-connections` | PASS; 174 subject topics, 173 settled outcomes and this planned topic pending |
| `git diff --check` | PASS |
| Source/aggregate/pin/root-README diff against `docs/publish-v1-upgrade` | PASS; no changes |

The explicit pending-topic argument reflects the new topic's planned status.
Its subject link is required now; its outcome-guide entry belongs to a later
completed/settled result or verified integration. No checker is modified and
no completed outcome is fabricated to make the default check pass.

The root README, figures, public input APIs, Lean sources and pins remain
unchanged. No asset regeneration or new proof baseline is claimed.

## Open Implementation Work

At the planning milestone all stages were unstarted. They are now implemented;
see [results](results.md), [caller obligations](caller-inventory.md) and the
implementation acceptance above for current checks and status.
