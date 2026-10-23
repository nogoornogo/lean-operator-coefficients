# README Connection-Map Follow-Up

The authorized README follow-up updates two maps to expose the implemented
field correspondence as an optional construction/transport route. It changes
navigation, not the statements or scope of the proved results.

## Figures And Tables Reviewed

| README item | Decision |
| --- | --- |
| Input Interfaces | Added the exact selected-field dictionary. Dashed routes distinguish mixed coefficient transport and jet/selected-source transport; the existing full input supplies the relations. Source selection also names coordinate reexpression. |
| Concrete Model Inputs | Added the inclusion/extraction-based construction before the remaining model-to-input checks. Both inverse laws and derived extraction covariance are explained in the ordinary-link index. A vertical layout keeps labels readable. |
| Finite Structural Classifications | Unchanged. The supplied domain, 572/326/246 partition and derivative-free minima are unaffected. The maintained SVG passes its freshness check. |
| Constraints on Model Inputs | Unchanged. The fixed-family mass-existence criterion and combined-request conditions remain the same; the shared construction does not establish an arbitrary model's missing premises. |
| Independent Proofs and Exploration Results | Unchanged. The new route belongs to input construction and does not close the stopped analytic SU(6) or group-foundation boundaries. |
| Input table and displayed theorem formulas | Reviewed unchanged. The existing operator and density entries remain the public input formats; a selected-field dictionary is an optional adapter. |

The added nodes link to the [field-connection dossier](../../proof/current/inputs/Physics/FIELD_CONNECTIONS.md)
and ordinary links also provide the [usage guide](input-guide.md).

## Verification

Both changed Mermaid diagrams render successfully with the existing local
Mermaid 10.9.5 and Chromium. Screenshots were visually inspected at a
1400-pixel viewport: nodes, edge labels and arrowheads are readable without
clipping. The 28 Mermaid `click` destinations across README all have ordinary
Markdown link counterparts. Hosted GitHub rendering/click behavior was not
tested; ordinary links provide independent navigation.

| Check | Result |
| --- | --- |
| Local Mermaid/Chromium rendering and visual inspection | PASS; both changed diagrams |
| Mermaid destination/ordinary-link comparison | PASS; all 28 destinations |
| `node tools/docs/render-structural-classification.mjs --check` | PASS; unchanged SVG matches 572 inputs, 326 allowed, 246 forbidden |
| `node tools/docs/check-links.mjs` | PASS; local links and anchors |
| `python3 tools/docs/check-topic-index.py` | PASS |
| `python3 tools/docs/check-work-metadata.py` | PASS |
| `git diff --check` and staged whitespace check | PASS |

No Lean build was rerun. Lean sources, aggregates, assumptions, dependency
pins and generated classification data are unchanged by this documentation-only
follow-up. Temporary preview HTML, screenshots and browser profiles remain
outside source control. No rendering tool or project dependency was installed.
