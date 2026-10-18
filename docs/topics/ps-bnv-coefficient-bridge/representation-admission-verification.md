# Representation Admission Verification

- Branch: proof/ps-bnv-coefficient-bridge; base checkpoint 01; no master merge.
- Focused `lake build GUT.PatiSalam.Audit.AuditRepresentationAdmission`:
  success, 3134 jobs; 40 strict transitive axiom checks and model import boundary
  passed. Only propext, Classical.choice and Quot.sound accepted.
- Serialized full `lake build`: success, 6654 jobs; no warning/error diagnostics.
- `node tools/layout/check-layout.mjs`: 1327 modules; all checks passed.
- `node tools/docs/check-links.mjs`: 608 Markdown files, 3849 local inline links,
  89 heading fragments; zero errors.
- `git diff --check`: clean before commit.
- Earlier exact scripts were not rerun: their mass, vertex, normalization and
  test definitions were unchanged. New arbitrary-group identities are proved
  in Lean and audited; no sampled group test is used as a premise.
- No dependency pins, heartbeat limits, custom axioms or audit exceptions changed.
  Initial elaboration failures and unused simp diagnostics were corrected.

See the [result](representation-admission-result.md) for exact group, dual-index,
right-handed-field and remaining action-matching boundaries.
