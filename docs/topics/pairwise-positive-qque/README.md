# Pairwise Positive Constituents For Qque

- ID: pairwise-positive-qque
- Status: completed
- Result type: proved, retaining normalized species-index inputs.
- Working branch: `proof/pairwise-positive-qque`.
- Integration target: `master` after proof and audit gates.

## Frozen Endpoint

Replace the single constituent shared by Q/up/e with two possibly different
constituents: i with positive Q/up coefficients and k with positive Q/e
coefficients. Keep the normalized finite continuous irreducible family,
three actual species-index equations and continuous compatible SM-cover x H
action on the unchanged radical. H remains compact. Derive the split maps,
not assume them at the source endpoint.

Construct a Q-symmetric invariant coefficient from the two evaluation
pairings; prove its actual-field spinor/alternating and exterior descents
nonzero. The same Q field is used twice. Do not require i = k, i != k,
extra generations, orthogonal splitting maps, or exchange/nonzero certificates.
Prove recovery of the old shared-positive condition.

## Steps And Stop Condition

1. Construct the two-pair symmetric coefficient and a nonzero diagonal witness.
2. Prove nonzero spinor/exterior descent and transport to actual fields.
3. Extract the two pairs of splits from actual species indices and assemble
   the final theorem, preserving the old endpoints.
4. Audit an example with pairwise but no three-way positive support, equal-
   constituent recovery and missing-pair controls; run strict axiom audits,
   full/focused builds, layout/links and the exact qque computational test.

Stop at those endpoints. No automatic irreducible normalization, new GUT
model, arbitrary embedding classification, MFV spurions or dynamics. A new
theorem-level prerequisite or changed physical input requires reassessment.
Pins and the E6 literature boundary remain unchanged.

## Result

All four steps are complete. [Results and boundaries](results.md) describe
the new symmetric two-pair coefficient, its nonzero exterior descent,
species-index extraction and actual-field endpoints. Equal and different
constituents use the same proof; no orthogonality or extra generation premise
was added. The old shared-positive condition implies the new pairwise one.

The checked Circle field model Q=1+z, up=1, e=z has pairwise but no three-way
positive support. Its actual multiplicity characters match that profile, and
its explicit SM/spinor exterior coefficient is nonzero. This control is not
an ambient GUT/mass/radical construction. No scoped obligations remain; the
non-goals above are not silently reopened.

## Verification And Integration

- Focused builds: `Math.RepresentationTheory.Audit.AuditPairwiseInvariantPairing`
  and `Physics.StandardModel.Operators.Audit.AuditPairwisePositiveQque` passed.
- Strict transitive axiom checks: 8 mathematical and 16 physical declarations,
  including endpoints, equal-constituent recovery and concrete controls; only
  `propext`, `Classical.choice`, `Quot.sound` allowed. Source-layer audits pass.
- `lake build`: passed, 5708 jobs. Existing warnings remain; no warnings from
  the six new Lean modules. Initial audit elaboration errors were repaired
  before the passing build, without weakening the audits.
- `node tools/layout/check-layout.mjs`: 663 modules, all checks passed.
- `python3 tools/qque/audit_one_generation.py`: 4 exact tests passed.
- `python3 tools/qque/audit_pairwise.py`: 3 exact tests passed; exhaustive
  comparison for 32 component generators, not a proof oracle or GUT model.
- `node tools/docs/check-links.mjs`: 269 Markdown files, no errors.
- `git diff --check`: passed.

Lean LSP MCP was unavailable; source reads and focused/full builds were used.
Dependency pins and the E6 literature boundary are unchanged. Logs and Python
bytecode are not source-controlled. Git ancestry records the topic and no-ff
merge into `master`; retain the topic branch and verify the merged state.
