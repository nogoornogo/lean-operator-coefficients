# Upgrade Notice And README Result Maps

- ID: `publish-v1-upgrade`
- Status: completed
- Result type: documentation with separately verified child proof integrations
- Working branch: `docs/publish-v1-upgrade`
- Integration target: `refactor/higgs-cubature-structure`
- Authorization: user-requested notice for `publish/v1.0` users and README figure/table updates
- Parent exception: bounded documentation child of the structural-cubature refactor;
  later chain integration into master was explicitly authorized; publication is separate

## Endpoint And Scope

Provide a reader-facing upgrade notice, linked from README, comparing the
local `publish/v1.0` tag with the development tree. Explain added derivative,
EOM/IBP and Lagrangian routes, dependency changes, registered source
compatibility and migration. Preserve existing README claims and their scope.
Do not label development changes as a new published release.

Refresh README input/result maps and the existing structural-classification
figure against current canonical paths and APIs. The earlier maps are on the
separate unmerged `docs/input-interface-flow` branch. Adapt only their README
presentation and figure generator/asset; do not integrate that branch's Lean
templates, audits or work records. This original documentation endpoint changes
no Lean sources, pins or theorem statements; later proof children are listed below.

## Plan And Acceptance

1. Compare the publication tag, current pins and compatibility registry;
   confirm migration examples against the canonical and forwarding sources.
2. Write a concise upgrade guide and link it from README. Keep removal policy
   and model/theorem boundaries explicit; link technical details.
3. Adapt the five README maps/figures, provide ordinary links for Mermaid
   nodes, and align the input table with canonical imports and namespaces.
4. Regenerate the SVG from current count statements; check its data and
   freshness, parse the Mermaid diagrams and inspect rendered figures.
5. Run local-link, topic-index, work-metadata and whitespace checks; review
   the scope and commit the verified documentation endpoint. No Lean build
   is required or claimed for documentation-only changes.

## Result And Verification

The [upgrade notice](../../UPGRADING.md) explains the toolchain transition,
optional new inputs, compatibility scope, migration examples and rebuilding.
It distinguishes development changes from a published release and retains
the derivative-free scope of the existing finite minima.

[README](../../../README.md) links the notice and includes four Mermaid
maps, the regenerated classification SVG and canonical imports in its input
table. At the original documentation acceptance, all 26 diagram link
destinations also had ordinary Markdown links; the later
[field-connection map follow-up](../model-input-connections/readme-verification.md)
records the updated routes and rendering.
The renderer reads canonical source paths and uses current Physics names.
The separate input-flow branch and its Lean examples remain unmerged.

[Verification](verification.md) records successful rendering, count/freshness,
local-link, topic, metadata and whitespace checks for the original documentation
endpoint. No Lean build was rerun for that endpoint; its source and pin review
does not describe the later proof integrations below.

The documentation endpoint and its proof children are integrated through the
recorded parents into master. [Master integration verification](../source-api-compatibility/master-integration.md)
records the checks and README follow-up. Remote publication has not been
performed. There is no remaining required work within this endpoint.

## Integrated Child Topics

This branch also contains two completed proof children. Their own records
define the theorem scope and merged-state checks; they are separate from the
documentation acceptance above.

| Child | Integrated result and evidence |
| --- | --- |
| [SU(6) protection feasibility](../su6-protection-feasibility/README.md) | Standard-class obstruction and algebraic boundary-amplitude construction; [parent integration checks](../su6-protection-feasibility/integration-verification.md). |
| [Field, selection and symmetry connections](../model-input-connections/README.md) | Exact selected-field dictionaries and coefficient/jet/full-relation transports; [parent integration checks](../model-input-connections/integration-verification.md). |

The [upgrade guide](../../UPGRADING.md) includes these additive inputs and
model results. The branch therefore contains Lean additions as well as its
original documentation work. Published input compatibility and dependency
pins are preserved. The complete chain was subsequently integrated through the
recorded `refactor/higgs-cubature-structure` parent into master under the user's
explicit direction; the children's original acceptance records retain their
own scope.

## Maintenance Policy Follow-Up

The user additionally requested durable rules for namespace ownership,
README/graph synchronization, numerical-proof prohibition and repetitive
case-file prohibition. These are documented in [AGENTS.md](../../../AGENTS.md),
the [layout policy](../../architecture/MODULE_LAYOUT.md#imports-and-names),
[README maintenance](../../architecture/WORKFLOW.md#readme-figures-and-tables)
and the [structural proof policy](../../architecture/PROOF_ENGINEERING.md).
The workflow, proof-dossier conventions and tool guide link the same rules.

The proof policy applies to new proofs and substantive rewrites. Small exact
supporting identities retain their stated structural role; retained checked
proofs are not rewritten by this documentation task. README's current claims,
four diagrams, input table and SVG are reviewed unchanged. Documentation checks
pass; no Lean build is rerun. See the
[verification follow-up](verification.md#maintenance-policy-follow-up).

## References

- [Source compatibility and migration](../source-api-compatibility/migration-guide.md).
- [Current build and dependency pins](../../architecture/BUILD.md).
- [Derivative interface](../derivative-interface-adapters/input-guide.md).
- [Invariant density input](../euler-naturality/input-guide.md).
- [Fresh-compilation audit](../proof-memory-audit/README.md).
- [Structural Higgs cubature](../higgs-cubature-structure/README.md).
