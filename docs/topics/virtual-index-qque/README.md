# Positive-Dimension Virtual Indices To Qque

- ID: virtual-index-qque
- Status: completed
- Result type: proved, with an explicit normalized virtual-presentation input.
- Working branch: `proof/virtual-index-qque`.
- Integration target: `master`, after the endpoint and audit gates close.

## Frozen Endpoint

Replace the common positive actual residual target by a finite virtual
character with positive total dimension. Use a normalized presentation:
finitely many pairwise inequivalent finite-dimensional continuous irreducible
H representations and integer coefficients, including negative coefficients.
Do not assume a positive component, common quotient, splitting or operator.
Derive those outputs from the signed character equations and positive dimension.

H remains compact with continuous actions. Keep the existing compatible
SM-cover x H action on the unchanged mass radical. Establish an actual-field
qque alternating/exterior endpoint from common virtual species indices; then
connect it to two actual conjugations through explicitly stated weight/species
index compatibility. Neither equal dimensions alone nor arbitrary extra light
matter suffices. Exact SM-only spectra are not required by the new core.

Normalized virtual data describes the proposed index, not a decomposition of
the actual light fields. Constructing this normal form automatically from any
pair of representations is not to be silently assumed or claimed. Preserve
the old positive-target and exact-spectrum entry points. Record precisely any
recovery interfaces actually proved.

## Steps And Gates

1. Formalize finite virtual character evaluation, dimension, positive-component
   existence and compact character pairing extracting its integer coefficient.
2. Derive common split quotients from matching actual differences of characters.
3. Apply the existing SM field extraction and spinor/exterior construction;
   connect the actual conjugation route without replacing index compatibility
   by a dimension-only condition.
4. Audit signed examples, zero/negative-dimension boundaries, the actual-field
   endpoint's hypotheses and transitive axioms. Run focused/full builds,
   layout/link checks and the existing one-generation qque computation.

Stop if a new physical input, dependency or foundational project is needed.
No amplitude, realistic spectrum, anomaly consistency or new embedding claim.
The E6 literature boundary and all pins remain unchanged. Lean LSP MCP is not
available in this session; use source search and focused builds.

## Result And Stop Condition

All four steps are complete. [Results and boundaries](results.md) describe
the signed character/Hom theorem, actual common split extraction and the
actual-field alternating/exterior endpoint. Two conjugations derive common
virtual characters from the retained weight/species compatibility inputs.
The common-index entry also works without separate conjugation premises.

The Circle control 2-z has positive dimension, a negative coefficient, an
actual-difference realization and a split quotient, but provably no actual
continuous representation with that character. This is an extraction-level
control, not an end-to-end GUT example.

No obligations remain inside the frozen endpoint. Automatic normalized
decomposition of arbitrary representation differences, a concrete signed
GUT source, and reduction of character matching to particle counts are not
completed or implicitly launched. The prior exact-spectrum endpoint remains
the count-based entry for its narrower spectral class. No pins or literature
trust boundaries changed.

## Verification

- Focused builds of
  `Math.RepresentationTheory.Characters.Audit.AuditCompactVirtualCharacter`
  and `Physics.StandardModel.Operators.Audit.AuditVirtualIndexQque`: passed.
- Strict transitive axiom checks: 20 mathematical and 7 physical declarations;
  only `propext`, `Classical.choice`, `Quot.sound` allowed. These cover the
  actual final endpoints and signed controls, not just intermediate statements.
- `lake build`: passed, 5699 jobs; pre-existing dependency/source linter
  warnings remain, with no warnings from the six newly added modules.
- `node tools/layout/check-layout.mjs`: 654 modules, all checks passed.
- `python3 tools/qque/audit_one_generation.py`: 4 exact computational tests
  passed; these are independent cross-checks, not Lean proof premises.
- `node tools/docs/check-links.mjs`: 265 Markdown files, 1495 local inline
  links, no errors at verification.
- `git diff --check`: passed.

Integration target remains `master`; Git ancestry records the final topic
commit and merge. Retain the topic branch. Disposable build logs stay outside
source control.
