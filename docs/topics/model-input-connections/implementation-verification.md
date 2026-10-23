# Implementation Acceptance

## Scope And Resource Gates

Eleven new implementation modules and three persistent audits are registered
in the owning aggregates. Existing sources, dependency pins, proof limits and
axiom allowances are unchanged. New imports respect Math → Physics → GUT
ownership. `check-layout.mjs` reports 4,263 modules and passes.

All new implementation sources were freshly elaborated with
`lake env lean -j2 <source>.lean`, one compiler at a time, with disabled core
dumps, a 16 GiB address-space limit and 540 seconds per command. Imported
dependencies were reused. This is source elaboration, not a claim of rebuilding
the dependency closure from scratch.

## Fresh Implementation Elaboration

Peak RSS was obtained from POSIX `wait4` resource usage for each serialized
compiler command; time is elapsed wall time. The temporary measurement driver
and logs are disposable build output. GiB means 1,048,576 KiB. Measurements
cover only these sources and imported artifacts, not a universal solver bound.

| Source | Result | Seconds | Peak RSS, GiB |
| --- | --- | --- | --- |
| `Math/RepresentationTheory/Fields/Selection.lean` | PASS | 2.69 | 2.23 |
| `Math/RepresentationTheory/Fields/Interactions.lean` | PASS | 2.58 | 2.44 |
| `Math/RepresentationTheory/Fields/DerivativeConnection.lean` | PASS | 3.30 | 3.35 |
| `Math/RepresentationTheory/Fields/JetConnection.lean` | PASS | 3.85 | 3.35 |
| `Math/RepresentationTheory/Fields/Controls.lean` | PASS | 2.55 | 3.73 |
| `Physics/FieldTheory/Fields/SelectedFields.lean` | PASS | 2.79 | 3.67 |
| `Physics/FieldTheory/Fields/SelectionControls.lean` | PASS | 2.56 | 3.79 |
| `Physics/FieldTheory/Jets/Lagrangian/FieldInputConnection.lean` | PASS | 3.17 | 3.79 |
| `Physics/StandardModel/Spectrum/Representations/LeptonParityFieldConnection.lean` | PASS | 4.34 | 3.88 |
| `Physics/StandardModel/Operators/BaryonOne/Qque/S3FieldConnection.lean` | PASS | 2.58 | 3.70 |
| `GUT/SU6/Boundary/FieldConnection.lean` | PASS | 7.99 | 4.11 |

These direct elaborations emit no source diagnostics. Lake additionally
reports module-system import-style notices for the new legacy-style modules
and replays existing deprecated-import/linter messages from dependencies.
No warning or audit requirement is suppressed.

## Strict Transitive Audits And Regressions

The three new audits inventory every
declaration owned by the eleven new modules, including private/generated
declarations. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
They also enforce Math/Physics import ownership and normalize historical module
origins. Existing boundary, Lagrangian-model and Euler-naturality audits are
rerun independently as regressions.

Each command below was executed directly with `lake env lean -j2`, rather
than relying on saved Lake output:

| Audit source | Result |
| --- | --- |
| `Math/RepresentationTheory/Fields/Audit/AuditFieldConnections.lean` | PASS; 161 strict transitive checks |
| `Physics/FieldTheory/Fields/Audit/AuditFieldConnections.lean` | PASS; 85 strict transitive checks |
| `GUT/SU6/Audit/AuditFieldConnection.lean` | PASS; 92 strict transitive checks, including the exact sterile dictionary |
| `Math/RepresentationTheory/Constructions/Audit/AuditEulerNaturality.lean` | PASS; 310 strict transitive checks |
| `Physics/FieldTheory/Jets/Scalar/Inputs/Audit/AuditEulerNaturality.lean` | PASS; 9 strict transitive checks |
| `GUT/SU6/Audit/AuditBoundaryProtection.lean` | PASS; 295 strict transitive checks |
| `Physics/FieldTheory/Jets/Lagrangian/Audit/AuditLagrangianModel.lean` | PASS; 176 strict transitive checks |

## Aggregate And Documentation Gates

The serialized `lake build Math` and `lake build Physics` pass with 7,478 and
7,084 jobs respectively. The final `lake build` passes with 9,760 jobs. These are incremental
aggregate builds: unchanged dependencies and proof artifacts can be replayed.
Fresh-source measurements above are separate evidence.
Completion-record edits after these builds are documentation-only; no further
Lean build was rerun for those edits.

Local links, layout, topic navigation, work metadata and diff checks pass.
At this implementation acceptance the completed endpoint was unmerged and had
a short outcome-guide entry. The later authorized parent merge has separate
[integration verification](integration-verification.md); master integration
and remote push are outside both acceptance records.

| Final repository gate | Result |
| --- | --- |
| `node tools/layout/check-layout.mjs` | PASS; 4,263 modules |
| `node tools/docs/check-links.mjs` | PASS; no broken local links/anchors |
| `python3 tools/docs/check-topic-index.py` | PASS; subject and settled-outcome navigation |
| `python3 tools/docs/check-work-metadata.py` | PASS; portable records |
| `git diff --check` and staged whitespace check | PASS |
| Published Lean sources and pin/root-README review | Only new source/audit files and aggregate imports; pins and root README unchanged |
At implementation acceptance the root README and its figures were reviewed
unchanged; the input map linked the new dossier and guide. The subsequently
authorized [README follow-up](readme-verification.md) now exposes the shared
connection in its input and model maps, with separate documentation checks.

The source/location comparisons and the complete artificial-control matrix
are in [literature validation](literature-validation.md). The central
bibliography and existing source-ledger rows link the resulting comparisons;
test logs and module counts stay in this topic.
