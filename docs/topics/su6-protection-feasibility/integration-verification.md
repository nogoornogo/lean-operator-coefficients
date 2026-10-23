# Parent Integration Verification

The user explicitly authorized integration of the completed topic before
starting a separate generalization. The integration target was the recorded
`docs/publish-v1-upgrade` parent. The parent was an ancestor of the verified
topic endpoint and had no independent advance. The checkout was clean and
no other worktree used either branch.

`git merge --no-ff proof/su6-protection-feasibility` integrated both the
standard-class feasibility result and the algebraic boundary construction.
No conflict resolution or Lean/pin change was needed. This integration does
not merge the parent's earlier documentation/refactor chain into master.

## Merged-State Acceptance

All Lean checks used `-j2`, a 16 GiB address-space cap, disabled core dumps
and a 540-second timeout per command. Direct audits ran sequentially before
the full aggregate build.

| Check | Result |
| --- | --- |
| `git diff --exit-code proof/su6-protection-feasibility HEAD -- Math Physics GUT Math.lean Physics.lean GUT.lean lean-toolchain lakefile.lean lake-manifest.json` | PASS; sources and pins match the verified topic endpoint |
| `lake env lean -j2 GUT/SU6/Audit/AuditProtectionFeasibility.lean` | PASS; 19 strict transitive declaration checks |
| `lake env lean -j2 GUT/SU6/Audit/AuditBoundaryProtection.lean` | PASS; 295 strict transitive declaration checks |
| `lake env lean -j2 GUT/SU6/Audit/AuditPhysicalIndexObstruction.lean` | PASS; 12 strict transitive declaration checks |
| `lake build` | PASS; 9,746 jobs, incremental build with reusable dependency artifacts and replayed output |
| `node tools/layout/check-layout.mjs` | PASS; 4,249 modules, layer/import/cycle/aggregate/relocation checks |
| `node tools/docs/check-links.mjs` | PASS; no broken local links or anchors |
| `python3 tools/docs/check-topic-index.py` | PASS; subject and outcome navigation consistent |
| `python3 tools/docs/check-work-metadata.py` | PASS; portable work records |
| `git diff --check` | PASS |

The direct audits permit only `propext`, `Classical.choice` and `Quot.sound`.
Existing import/deprecation and lint warnings are replayed; no warning is
suppressed and no allowlist is relaxed. This is a merged-state check, not a
fresh compilation audit of every project source.

The [source register](references.md) is reconciled with the
[related-literature list](../../proof/RELATED_LITERATURE.md#su6-model-construction-boundary).
The root README and its diagrams/tables remain unchanged by the integration;
its model-specific conclusions are documented in the linked study instead.
Final integration-record edits are documentation-only; no further Lean build
is claimed for those edits.

## Result And Boundaries

The recorded parent contains both verified phases. The actual SU(6) admission
obstruction and the different boundary-amplitude mechanism retain their
respective hypotheses. Analytic mixed-mode admission, full brane-action
matching, quantum protection and numerical phenomenology remain outside the
completed algebraic endpoint.

No push, master integration, remote branch deletion or history rewrite was
performed. The new generalization is a separate topic, with its own contract
and implementation evidence.
