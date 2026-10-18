# Earlier Checkpoint Verification

These results belong to their respective earlier source states.

## Covariant Interface

Commands and final results:

- `lake build GUT.SU6.SelectionRules.Audit.AuditAutomorphismCovariantModel`:
  passed, 3,992 jobs; 8 Math + 10 GUT strict transitive checks.
- `lake build`: passed, 6,551 jobs on the final source state. No new warnings.
- `node tools/layout/check-layout.mjs`: 1,224 modules, all checks passed.
- `node tools/docs/check-links.mjs`: 499 Markdown files, 3,314 inline links,
  85 heading fragments, zero errors.
- `git diff --check`: passed; final source, hypotheses and documentation reviewed.

## Exterior Bridge

- `lake build GUT.SU6.SelectionRules.Audit.AuditCovariantFourFermion`: passed,
  4,011 jobs; 8 Math + 5 GUT strict transitive checks.
- `lake build`: passed, 6,555 jobs on the final source state; no new warnings.
- `node tools/layout/check-layout.mjs`: 1,228 modules, all checks passed.
- `node tools/docs/check-links.mjs`: passed, zero errors.
- `git diff --check`: passed; final source and support hypotheses reviewed.

## Exact Reversal

Verification:

- `lake build GUT.SU6.SelectionRules.Audit.AuditChargeReversingCandidate`:
  passed, 4,025 jobs; 2 Math + 3 Physics + 3 GUT strict transitive checks.
- `lake build`: passed, 6,561 jobs on final source state; no new warnings.
- `node tools/layout/check-layout.mjs`: 1,234 modules, all checks passed.
- Markdown links and `git diff --check`: passed, zero errors.
- Actual SM hypercharges/dimensions and the cover-versus-embedding boundary
  reviewed. No axiom exception, dependency change or master merge.

## Pointwise Gauge Comparison

Verification:

- Focused Math/GUT builds: 9 + 3 strict transitive checks passed.
- `lake build`: passed, 6,565 jobs on the final source state.
- Layout: 1,238 modules passed; Markdown links: 506 files, zero errors.
- `git diff --check`: passed; hypotheses and final diff reviewed.
- Dependency pins and audit allowances unchanged.
