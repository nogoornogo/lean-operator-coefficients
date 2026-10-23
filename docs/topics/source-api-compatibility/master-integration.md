# Master Integration Of The Compatible Source Series

The user explicitly authorized integration of the complete recorded branch
chain through master, followed by necessary README maintenance. Every target
was an ancestor of its child, with no independent advance. The initial
checkout was clean. No target branch was in use by another worktree; unrelated
detached worktrees were left untouched.

## Integration Chain

Each integration used `git merge --no-ff` with no conflict resolution. After
each merge, `git diff --exit-code <child> HEAD` confirmed an identical file
tree, including sources, tools, documentation and dependency pins.

| Completed child | Recorded target |
| --- | --- |
| `docs/publish-v1-upgrade` | `refactor/higgs-cubature-structure` |
| `refactor/higgs-cubature-structure` | `refactor/proof-memory-audit` |
| `refactor/proof-memory-audit` | `refactor/source-api-compatibility` |
| `refactor/source-api-compatibility` | `master` |

The upgrade branch already contained the verified
[SU(6) feasibility/boundary topic](../su6-protection-feasibility/integration-verification.md)
and [shared-field connections](../model-input-connections/integration-verification.md).
The separate `docs/input-interface-flow` branch and its Lean templates/audits
are not integrated. Its earlier README presentation was independently adapted
by the upgrade topic, as recorded there.

## Master-State Proof And Compatibility Checks

All [30 focused source checks](master-audits.md) pass directly on master.
They include legacy input/structure/restriction clients, original proof-memory
audits, both structural cubature inventories, the original Higgs completeness
consumers, shared field connections, Euler/Lagrangian regressions and SU(6)
admission/boundary checks. They use the unchanged two-thread convention,
16 GiB address-space cap, 540-second timeout and disabled core dumps.

One subsequent serialized `lake build` passes all 9,760 jobs. This is an
incremental aggregate build with reused dependency artifacts and replayed
output. The direct checks above rerun their source/audit code; this integration
does not repeat the earlier whole-project fresh compilation measurement.
Existing module-system import notices, deprecation warnings and linter messages
remain visible. No proof limit, axiom allowance, theorem hypothesis or pin is
changed during integration.

| Master-state comparison | Result |
| --- | --- |
| `python3 tools/layout/check-source-api.py` | PASS; 1,677 deprecated import facades and 12,989 protected aliases |
| `python3 tools/layout/check-source-transform.py` | PASS; 4,218 frozen source paths, five separately reviewed compatibility utility/consumer files, 37 checksum-guarded additions and exact aggregate imports |
| `python3 tools/layout/check-source-references.py <baseline-metadata>` | PASS; 2,540 canonical reference sets and occurrence sequences; 606 exact proof-body replacements, 16 scheduling references and one original proof split accounted for |
| `node tools/layout/check-math-namespaces.mjs` | PASS; 2,003 Math modules and 4,227 historical correspondences |
| `SOURCE_API_EXPORT=<temporary-json> lake env lean -j2 tools/layout/ExportSourceAPI.lean` | PASS; 72,778 repository constants exported from the complete merged environment |
| `python3 tools/layout/check-audit-counts.py <baseline-log> <master-log> --baseline-constants <baseline-json> --rebuilt-constants <master-json>` | PASS; all 422 original count records, five exact helper/source-extension reconciliations and retained public parents |
| `node tools/layout/check-layout.mjs` | PASS; 4,263 modules, layers/imports/cycles/aggregates/relocations |
| `python3 tools/layout/test-source-generators.py` | PASS; ten producers reproduce 149 canonical outputs without repository writes |
| `python3 tools/layout/test-source-api.py` | PASS; three compatibility-tool controls |
| `python3 tools/layout/test-audit-inventory.py` | PASS; five inventory-boundary controls |
| `python3 tools/layout/test-source-additions.py` | PASS; four additive-source/import rejection controls |
| `python3 tools/lean-memory/test-profile-project.py` | PASS; seven profiler controls |
| `python3 tools/lean-memory/test-rewrite-registry.py` | PASS; five proof-boundary controls |
| `node --test tools/layout/test-check-layout.mjs` | PASS; layout/origin regressions |
| Nine `tools/derivative-literature/check-*.py` diagnostics | PASS; existing finite Higgs/scalar/Weyl convention, relation and rank checks |

Python verification commands use `PYTHONDONTWRITEBYTECODE=1`. Saved original
metadata is used for historical reference comparison; it is not a theorem
premise. The finite diagnostics supplement Lean checks and do not supply their
proof premises or a broader completeness claim.

## Exact Replay Preparation

The first replay reported only the three aggregate files as mismatches.
Their additional imports belonged to the two verified model children, which
postdated the frozen refactor. The original source bodies already matched.
Before integration, the children received exact source/import manifests, and
the tool was extended to check their 25 additions separately. Together with
the twelve structural additions, all 37 hashes and owning imports are checked.
Missing, extra, duplicate or wrong-layer imports, changed source hashes and
replacement of a frozen source are rejected. No old source/import comparison
or Lean audit predicate is removed. The
[tool guide](../../../tools/layout/README.md) links the manifests and controls.

## References, README And Documentation

The original refactors add no literature theorem premise. The two model
children's source registers are reconciled with their existing entries in the
[literature list](../../proof/RELATED_LITERATURE.md), preserving source inspection
and applicability limits.

README now links the SU(6) standard-class obstruction and boundary-selected
protecting input from its concrete-model section. Its independent-results
diagram describes the current obstruction/boundary results rather than only
the earlier stopped exploration. This changed diagram renders successfully
with existing Mermaid 10.9.5 and Chromium and was visually inspected at a
1,400-pixel viewport. All 28 diagram `click` destinations have ordinary README
link counterparts. Hosted GitHub interaction was not tested.

The other three Mermaid diagrams and the input table are reviewed unchanged;
they already expose the optional field connections and canonical inputs.
`node tools/docs/render-structural-classification.mjs --check` passes with
572 inputs, 326 allowed and 246 forbidden. No SVG regeneration is needed.
General theorem statements and derivative-free minimum-dimension scope stay
unchanged. Topic overviews now distinguish the completed integration from
their historical acceptance/measurement checkpoints.

Final integration records and README edits are documentation-only. Local
links, topic navigation, portable metadata and whitespace are checked after
these edits; no further Lean build is rerun for them. Detailed outcomes stay
in the owning topics, with a short entry in the outcome guide.

## Retained Boundaries

Registered source compatibility retains its published surface and temporary
deprecations. The fresh-memory and cubature measurements describe their own
recorded source snapshots; they are not universal resource bounds or a fresh
4,263-module compilation claim. The E6 literature boundary remains explicit.
The SU(6) boundary result ends at algebraic amplitudes and contractions, and
the field dictionaries require their stated inverse/equivariance conditions.
Analytic spectra, quantum protection, empirical viability and automatic
light-EOM extraction are separate from the completed statements.

## Outcome And Local Cleanup

The four branches in the chain are integrated into master. Each local branch
was deleted with `git branch -d` only after merged-state verification,
reachability from master, absence of worktree use and absence of pending
child targets were confirmed. Historical branch names remain in their topic
records. Unrelated branches and detached worktrees were left untouched.

Final local-link, topic-index, portable-metadata and whitespace checks pass.
No remote push, remote branch deletion, history rewrite or release publication
was performed.
