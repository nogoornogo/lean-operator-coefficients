# Documentation Checks

From the repository root, using Node.js (standard library only):

```sh
node tools/docs/check-links.mjs
node --test tools/docs/test-check-links.mjs
git diff --check
```

The checker inspects tracked and non-ignored new Markdown files, skips deleted
files and fenced code examples, and checks local inline link targets plus
fragments targeting ATX Markdown headings. It is independent of the Lean build.

It does not check external URLs, reference-style links, renderer-specific
extensions, or generated doc-gen4 HTML. It supports the repository's current
inline-link conventions, not arbitrary Markdown syntax. Review moved paths and
claim boundaries separately; passing links do not establish proof correctness.

## Structural Classification Figure

When an authorized README edit changes a route, API, namespace, result,
count or target link, update the affected diagrams/tables and their ordinary
links together. Regenerate affected assets, check freshness and inspect changed
diagram rendering. Record unaffected visuals as reviewed unchanged; unrelated
prose edits need no regeneration. The
[README maintenance rule](../../docs/architecture/WORKFLOW.md#readme-figures-and-tables)
defines the acceptance boundary.

The [README figure](../../docs/assets/readme/b1-minimum-dimensions.svg) is a
static SVG rendered with D3. It shows the 572 labeled derivative-free SM/Higgs
B1 inputs, the allowed/forbidden partition and exact minimum engineering
dimensions for the 326 allowed inputs. Forbidden inputs have no finite minimum.

```sh
node tools/docs/render-structural-classification.mjs
node tools/docs/render-structural-classification.mjs --check
```

Generation requires Node.js with the optional documentation tools `d3` and
`jsdom` available in its module search path. It was checked with Node 20.20.2,
D3 7.9.0 and jsdom 29.0.1. These tools are unnecessary for viewing the SVG or
building Lean; no Lean/Lake dependency was added. `--output <path>` can direct
generation or a freshness check to another file.
`--check` compares bytes; different D3/jsdom versions can change the output even
when the data agree. Use the recorded versions for byte-identical reproduction.
The SVG uses an opaque white card to keep its labels readable across viewer themes.

The generator reads `minimum_distribution` and `classified_count` in
[SMB1ExactMinima](../../Physics/StandardModel/Operators/Support/Dimension/SMB1ExactMinima.lean),
and `rows_length` in
[SMFiniteLeptonAssignments](../../Physics/StandardModel/Operators/Support/Decomposition/SMFiniteLeptonAssignments.lean).
It divides doubled grades by two and verifies the count sums. A JavaScript
reimplementation of the displayed Lean domain and neutrality test uses fixed
bounds `2 ≤ k ≤ 12` and odd `−17 ≤ L ≤ 17`, comparing its aggregate counts
with the theorem counts. This does not check equality of the Lean and JS
definitions; a domain change preserving the counts could go undetected.
It emits no proof input and does not recheck the Lean proofs or recompute
the minimum-dimension witnesses/lower bounds. The
[current theorem dossier](../../docs/proof/current/applications/Physics/SM_CHARGE_DEGREE_BOUNDS.md#complete-b1-minima-on-the-existing-572-assignments)
owns those semantics.

Rerun generation and `--check` when these theorem conclusions, the displayed
domain, labels, chart style or generator change. Source syntax changes that
cannot be parsed cause an error; they are not silently replaced by old CSV
values. Review the JS bounds when `candidatePairs` or `leptonRange 3` changes,
and review the fixed field/action assumptions separately. The figure is maintained
only as a generated asset; its data are not edited by hand.
