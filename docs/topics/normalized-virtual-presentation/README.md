# Automatic Normalized Virtual Presentations

- ID: normalized-virtual-presentation
- Status: completed
- Result type: proved; positivity remains an input condition.
- Working branch: `proof/normalized-virtual-presentation`.
- Integration target: `master` after all gates pass.

## Frozen Endpoint

Keep compact H and jointly continuous finite-dimensional complex actions.
Construct a common finite family of continuous irreducibles, with no two
equivalent, for finitely many actual representations. Construct integer
coefficients for their differences and prove the character identities.
Apply this to actual SM species multiplicities and opposite-species duals,
so normalized presentation and species matching are outputs, not user inputs.
Positive pairwise support remains a sufficient condition to check; it is
not inferred for arbitrary spectra. No constructive decomposition algorithm,
new GUT model, compactness removal, or dynamics is promised.

## Bounded Steps

1. Reuse finite semisimple decomposition and inherited continuity.
2. Combine repeated constituents into one finite normalized presentation.
3. Construct species-index presentations and connect to the retained qque API.
4. Persistent strict axiom audits, focused/full builds, layout/link checks.

Stop at these interfaces. Do not reopen general representation classification
or E6 foundations. Keep all dependency pins and existing theorems unchanged.

## Result

All four steps are complete. The [result and boundaries](results.md) describe
the reusable finite-family construction, actual species-index presentation
and the new actual-field qque alternating/exterior endpoints. The user no
longer supplies a normalized family or species-matching certificates.
Positive support of the constructed indices remains a hypothesis.

## Verification And Integration

- Focused build of `Math.RepresentationTheory.Characters.Audit.AuditNormalizedPresentation`
  and `Physics.StandardModel.Operators.Audit.AuditAutomaticSpeciesQque`: passed.
- Strict transitive axiom audits: 21 mathematical and 7 physical declarations;
  only `propext`, `Classical.choice`, `Quot.sound` allowed. Layer audits pass.
- `lake build`: passed, 5715 jobs. Existing warnings remain; the seven new
  Lean modules have no warnings in the final build.
- `node tools/layout/check-layout.mjs`: passed, 670 modules.
- `node tools/docs/check-links.mjs`: passed, 272 Markdown files, no errors.
- `python3 tools/qque/audit_one_generation.py`: 4 exact tests passed.
- `python3 tools/qque/audit_pairwise.py`: 3 exact tests passed.
- `git diff --check`: passed; source and assumption diff reviewed.

Normalization edge cases are Lean-checked (repeated characters, signed
cancellation, negative coefficients, empty family). Existing Grassmann tests
are regression checks of the reused exterior construction, not normalization
oracles. Initial elaboration errors and excessive concrete type unfolding
were resolved by bundling the proved presentation; no heartbeat limit or
audit was weakened. Lean LSP MCP was unavailable. Source inspection and
focused/full builds were used instead. Pins and E6 boundaries are unchanged.

Commit and no-ff integration target is `master`; Git ancestry records the
actual integration. Retain the topic branch and recheck the merged state.
