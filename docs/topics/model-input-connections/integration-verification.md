# Parent Integration Verification

The user authorized integration of the completed shared-connection topic.
Its recorded target is `docs/publish-v1-upgrade`. The parent was an ancestor
of the verified child endpoint, with no independent advance. The checkout
was clean; neither branch was in use by another worktree. Other detached
worktrees were left untouched.

`git merge --no-ff proof/model-input-connections` integrated the field,
selection, interaction and coefficient/jet constructions together with their
controls, audits and README map follow-up. No conflict resolution, source
adjustment or dependency update was needed. This merges only into the recorded
parent, leaving its documentation/refactor chain outside master.

## Merged-State Acceptance

The seven direct audits ran sequentially with `lake env lean -j2`, followed
by `lake build`. Each command used a 16 GiB address-space cap, disabled core
dumps, `LEAN_NUM_THREADS=2` and a 540-second timeout. The direct audits were
freshly executed on the merged state rather than accepted from replayed
Lake output. Their imported dependencies were reused.

| Check | Result |
| --- | --- |
| Source, aggregate, pin and root-README diff against `proof/model-input-connections` | PASS; identical to the verified child endpoint |
| `lake env lean -j2 Math/RepresentationTheory/Fields/Audit/AuditFieldConnections.lean` | PASS; 161 strict transitive checks |
| `lake env lean -j2 Physics/FieldTheory/Fields/Audit/AuditFieldConnections.lean` | PASS; 85 strict transitive checks |
| `lake env lean -j2 GUT/SU6/Audit/AuditFieldConnection.lean` | PASS; 92 strict transitive checks |
| `lake env lean -j2 Math/RepresentationTheory/Constructions/Audit/AuditEulerNaturality.lean` | PASS; 310 strict transitive checks |
| `lake env lean -j2 Physics/FieldTheory/Jets/Scalar/Inputs/Audit/AuditEulerNaturality.lean` | PASS; 9 strict transitive checks |
| `lake env lean -j2 GUT/SU6/Audit/AuditBoundaryProtection.lean` | PASS; 295 strict transitive checks |
| `lake env lean -j2 Physics/FieldTheory/Jets/Lagrangian/Audit/AuditLagrangianModel.lean` | PASS; 176 strict transitive checks |
| `lake build` | PASS; 9,760 jobs, incremental build with reusable artifacts and replayed output |
| `node tools/layout/check-layout.mjs` | PASS; 4,263 modules |
| `node tools/docs/render-structural-classification.mjs --check` | PASS; 572 inputs, 326 allowed, 246 forbidden |
| `node tools/docs/check-links.mjs` | PASS; no broken local links or anchors |
| `python3 tools/docs/check-topic-index.py` | PASS; subject and outcome navigation consistent |
| `python3 tools/docs/check-work-metadata.py` | PASS; portable records |
| `git diff --check` | PASS |

The direct audits total 1,128 declaration checks and allow only `propext`,
`Classical.choice` and `Quot.sound`. The aggregate build replays existing
module-system import notices, deprecated-import/name warnings and linter
messages. No warning is suppressed and no audit allowance is relaxed. This
is not a fresh compilation of every project source.

## Documentation And References

The [source register](references.md) is reconciled with the existing Angelescu,
Dreiner–Haber–Martin and Sardanashvily entries in the
[related-literature list](../../proof/RELATED_LITERATURE.md). They link the
implemented comparisons and retain their inspection and applicability limits.
No external theorem premise or paper-wide validation is added.

The child README and result page now link this integration. The original
implementation acceptance remains a separately identified checkpoint. The
parent overview lists both integrated proof children and links their evidence;
the [upgrade guide](../../UPGRADING.md) includes the optional field adapters
and the algebraic SU(6) boundary result. The input guide spells out the
`coordinateJets` convenience wrapper's `Unit` bosonic alphabet and points to
`fieldEquiv` for arbitrary odd/even dictionaries.

These follow-up edits are documentation-only. Local links, topic navigation,
portable metadata and whitespace are checked again after the edits; no further
Lean build is rerun for them. The root README maps, input table, classification
figure and claims are reviewed unchanged. The child already supplied the
affected map updates and [rendering evidence](readme-verification.md).

## Result And Boundaries

The recorded parent contains the completed shared constructions and their
model/source/artificial controls. Two-sided field dictionaries, total-density
relations and the exact full-relation preimages retain their stated hypotheses.
`coordinateJets` is a convenience specialization; the general mixed transport
is `fieldEquiv`. Analytic spectrum identification, empirical viability and
automatic light-EOM extraction are not conclusions of this integration.

After merged-state verification, the local child branch was deleted with
`git branch -d` after confirming reachability from the parent, no worktree use
and no pending child target. Its historical name remains in the topic overview.
No master integration, push, remote branch deletion or history rewrite was
performed.
