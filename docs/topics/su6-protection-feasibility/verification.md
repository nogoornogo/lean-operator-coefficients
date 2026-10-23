# Standard-Class Feasibility Verification

This records the completed first phase. The subsequently authorized boundary
construction has its own [verification record](boundary-verification.md).

## Statement And Assumptions

The new proof composes the actual SU(6) radical-index theorem with faithful
cyclic characters and the existing actual infrared coefficient iff. The
standard embedding, product action, invariant symmetric mass and positive
pure-target hypotheses are retained. The light index is not substituted for
an exact full-SM field dictionary.

For the all-left Yukawa assignment `(q,-q-h,-q+h,l,-l+h)`, character equality
gives `q=-q-h` and `q=-l+h`. Their linear combination is `3q+l=0` for every
positive cyclic order, without division or case enumeration. Higgs charge
cancellation supplies an index gate only. The coefficient iff is used solely
at h=0 on its existing actual three-generation bounded domain.

All new consumers live in `GUT.SU6ProtectionFeasibility`. The phase dictionary
agrees with the existing scalar representations. Tests include the actual
lepton-parity mass/radical/Yukawa input, its all-degree derivative-free
prohibition and failed SU(6) target, the neutral allowed-input control, and
opposite S3 coefficient outcomes with the declared flavor-map obstructions.
No new representation rank table or external calculation is a proof premise.

## Lean Acceptance

Commands run from the repository root with `-j2`, a 16 GiB address-space cap,
core dumps disabled and a 540-second command timeout. No proof option, pin,
strict axiom allowlist or existing audit is changed.

| Command | Result |
| --- | --- |
| `lake build GUT.SU6.Audit.AuditProtectionFeasibility` | PASS; focused build, then final source additions checked in the full build |
| `lake env lean -j2 GUT/SU6/Audit/AuditProtectionFeasibility.lean` | PASS; 19 transitive checks over the new namespace, including generated helpers |
| `lake env lean -j2 GUT/SU6/Audit/AuditPhysicalIndexObstruction.lean` | PASS; 12 strict transitive checks |
| `lake env lean -j2 Physics/StandardModel/Spectrum/Representations/Audit/AuditInverseCyclicSMConstruction.lean` | PASS; 63 strict transitive checks |
| `lake env lean -j2 GUT/SU6/Audit/AuditOutsideResidualSamples.lean` | PASS; 24 strict transitive checks |
| `lake env lean -j2 Physics/StandardModel/Operators/Support/Coordinates/Audit/AuditSMSupportLFV.lean` | PASS; 361 strict transitive checks |
| `lake build` | PASS; 9,738 jobs, all three new modules and GUT aggregate compiled |

Every audit permits only `propext`, `Classical.choice` and `Quot.sound`.
The namespace audit asserts that the charged-Higgs gate and main concrete
consumers are included. A local proof-development rewrite error was corrected
before acceptance. The unavailable optional system timing executable was not
installed; commands used shell timing and the same guards instead.

The full build is incremental, with dependency/project cache replay. It is
not a fresh-compilation profile or fresh-clone reproduction. Existing
module-system/deprecation warnings are replayed; the GUT aggregate also emits
the retained TorusCharacter and UnitaryVirtualRestriction facade warnings.
No warnings or errors originate in the three added modules on final checks.

## Source Comparison And Documentation

The [source register](references.md) records the versioned HTML inspection
and its limits. The comparison of a published boundary-selection mechanism
with a finite-dimensional mass radical is a scope decision, not a formal
verification of that paper or a new external theorem input. No literature
coverage row is claimed for unproved paper-to-model admission. The related
literature list links the source and this boundary explicitly.

The [model guide](../../model-studies/su6-protection/feasibility.md), application
guide and GUT assumptions ledger agree with the Lean statements. The root
README, its four Mermaid diagrams, input table and classification SVG were
reviewed unchanged: this result does not add a protecting model to them.
No diagram rerendering or asset regeneration was needed.

| Repository check | Result |
| --- | --- |
| `node tools/layout/check-layout.mjs` | PASS; 4,241 modules, layer/import/cycle/aggregate/relocation checks |
| `node tools/docs/check-links.mjs` | PASS; no broken local links or anchors |
| `python3 tools/docs/check-topic-index.py` | PASS; topic and settled outcome indexed |
| `python3 tools/docs/check-work-metadata.py` | PASS |
| `node tools/docs/render-structural-classification.mjs --check` | PASS; unchanged 572-input figure is current |
| `git diff --check` | PASS |

No new full SU(6) realization, anomaly cancellation, realistic mass spectrum,
interacting EOM completeness, numerical simulation, matching or decay-rate
result is claimed. Other embeddings, noncommuting actions, non-pure targets
and boundary-selected modes require a separately frozen construction endpoint.
