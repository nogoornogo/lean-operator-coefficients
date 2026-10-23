# Upgrade Notice And Figure Verification

This page distinguishes the original documentation acceptance from later
documentation follow-ups. Proof children have separate merged-state records:
[SU(6) feasibility](../su6-protection-feasibility/integration-verification.md)
and [shared field connections](../model-input-connections/integration-verification.md).

## Source And Compatibility Review

Compared the local `publish/v1.0` README and dependency pins with the current
tree. The publication tag describes derivative-free inputs and pins Lean
4.35.0-rc3; the current tree pins 4.35.0, updates Mathlib/TauCeti and adds
Physlib. The earlier 572/326/246 classification is already present at the
publication tag and is described as retained, not newly proved.

Checked the migration examples against the frozen source-API path map,
canonical files and old forwarding modules. The Math prohibition namespace
is unchanged; the shared mass-spectrum namespace changes from GUT to Physics.
The guide links the registered compatibility boundary, including compiler
helpers and reflection, and does not promise binary artifact compatibility.
No shim is removed and no removal release is assigned.

The added scalar, Higgs and Weyl–Higgs dimensions and the all-order model
operations are linked to their result statements. Free-sector completeness
is not transferred to interacting equations. The density route retains
constant linear actions, local finite polynomials and ordinary derivatives.

## README Maps And Generated Asset

The prior README maps and figure renderer were read from the separate
`docs/input-interface-flow` branch. Only the presentation and renderer are
adapted here. Its Lean templates, aggregate additions, audits and topic
records are not imported. The input map instead links current available
guides, and the input table names canonical imports.

All four Mermaid diagrams rendered successfully with local Mermaid 10.9.5
and Chromium and were visually inspected at a 1400-pixel viewport. All
26 `click` destinations have exact ordinary Markdown link counterparts in
README, whose files/anchors pass the repository link check. Hosted GitHub
rendering and click interaction were not tested; the ordinary links provide
navigation independently of that behavior.

The SVG was regenerated with Node 20.20.2, D3 7.9.0 and jsdom 29.0.1, then
rendered and visually inspected. The renderer reads the canonical
`Physics.SMB1ExactMinima` and `Physics.SMFiniteLeptonAssignments` source files.
It checks the 572-input partition and the ten minimum-dimension bins.
The fixed-bound JavaScript reimplementation checks aggregate counts, not
definition equality or the Lean proofs. The [tool guide](../../../tools/docs/README.md#structural-classification-figure)
retains this boundary and version-sensitive byte comparison. No optional
tool was installed and no project dependency was added.

## Acceptance Checks

| Check | Result |
| --- | --- |
| `node --check tools/docs/render-structural-classification.mjs` | PASS |
| `node tools/docs/render-structural-classification.mjs --check` | PASS; 572 inputs, 326 allowed, 246 forbidden |
| Local Mermaid/Chromium rendering | PASS; four diagrams and all ordinary link counterparts |
| SVG rendering and visual inspection | PASS |
| `node tools/docs/check-links.mjs` | PASS; no broken local links or heading fragments |
| `python3 tools/docs/check-topic-index.py` | PASS; subject and settled unmerged outcome indexed |
| `python3 tools/docs/check-work-metadata.py` | PASS |
| `git diff --check` | PASS |

No Lean build was rerun. This documentation-only change neither establishes
a new proof baseline nor modifies sources, assumptions, audits or dependency
pins. No new literature comparison or bibliography entry is introduced.
Preview HTML, screenshots and browser profiles remain outside source control.

## Maintenance Policy Follow-Up

The four requested rules are now recorded in the agent instructions and linked
architecture policies. Namespace ownership and compatibility requirements are
consolidated in the layout guide. README maintenance requires affected diagrams,
tables, generated assets and ordinary links to be updated in the same change.
Numerical/exhaustive case proofs and large families of repetitive calculations
are prohibited as the main proof design, including kernel-checked generated
tables. The supporting-identity boundary follows the completed structural
Higgs refactor; no tactic is banned merely by name.

Reviewed the existing policy text for contradictions. Replaced the layout's
old certificate-chunk instruction and the architecture index's outdated
namespace description; linked the structural policy from workflow and proof
dossier conventions. Existing finite certificates retain their own proof status.

The root README, its four Mermaid diagrams, table, SVG, renderer and input data
are unchanged by this policy follow-up. They were reviewed for impact; no new
rendering or regeneration was needed. Figure freshness, local links, topic index,
work metadata and whitespace checks pass. No Lean build was rerun. Proof
baselines, sources, dependency pins and audits remain unchanged.

## Integrated-Child Documentation Follow-Up

The parent overview now lists both integrated proof children, their results
and their own merged-state checks. Earlier source-unchanged and skipped-build
claims are explicitly scoped to the original documentation endpoint. The
upgrade guide adds selected-field constructors, full-input derivative/jet
transport and algebraic SU(6) boundary results with their admission limits.
The selected-field guide names the `coordinateJets` wrapper's `Unit` bosonic
alphabet and the general `fieldEquiv` alternative.

Local-link, topic-index, portable-metadata and whitespace checks pass after
these edits. No Lean source or pin is changed, and no further Lean build is
rerun for this documentation follow-up. The child integration record above
owns the completed merged-state full build and direct strict audits.

The root README maps, table, structural-classification figure and claims are
reviewed unchanged. Their existing field-connection update already exposes
the added route, and the classification freshness check passes. No rendering
is repeated for unchanged figures. The parent remains unmerged into its
recorded refactor target.

## Integration Source-Replay Preparation

Pre-integration replay found differences only in `Math.lean`, `Physics.lean`
and `GUT.lean`: their imports include the two subsequently verified proof
children, which were outside the frozen refactor's source inventory. The
older source bodies matched. The children now own exact source/import
manifests, and the replay checks all 25 additions separately with checksums
and exact owning-aggregate imports. No existing source comparison, axiom
allowlist or import-layer gate is relaxed.

Four negative-control tests cover changed sources, replacement of an existing
source, extra/missing/duplicate/wrong-layer imports, incorrect topic identity
and escaping paths. They pass. This is a verification-tool update; it changes
no Lean declaration or dependency pin. Final master integration checks have
their own evidence record.

## README Density-Invariance Clarification

The authorized README follow-up clarifies that the automatic density constructor
requires exact equality of the evaluated polynomial density. Invariance only
modulo total derivatives needs separate treatment. This describes the existing
`StandardDensityAction.model` hypothesis; no theorem or input API changes.

All four Mermaid maps, the input table and classification SVG are reviewed
unchanged. Their routes, labels, counts and links remain consistent, so no
rendering or asset regeneration is needed. Local-link, topic-index, portable-
metadata and whitespace checks pass. No Lean build was rerun for this
documentation-only clarification. The user authorized updating the existing
annotated `publish/v2.0` tag to include this committed clarification; its
existing change summary is retained. Remote tag updates are outside this action.
