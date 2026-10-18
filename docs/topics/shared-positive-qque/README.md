# A Shared Positive Constituent For Qque

- ID: shared-positive-qque
- Status: completed
- Result type: proved, retaining normalized species-index inputs.
- Working branch: `proof/shared-positive-qque`.
- Integration target: `master` after proof/audit gates close.

## Frozen Endpoint

Keep the normalized finite continuous irreducible virtual presentations and
the three actual SM-species index equations of the
[virtual-index route](../virtual-index-qque/results.md). Replace equality of
the three whole characters and positive total Q dimension by existence of one
index i with a_Q(i), a_up(i), a_electron(i) all strictly positive.

Derive common split quotients, actual participating fields and a nonzero qque
alternating/exterior coefficient. H remains compact and the compatible
SM-cover x H action on the unchanged radical remains continuous. No common
quotient, splitting or coefficient may be supplied as a premise.

This is a species-index entry; it need not take actual conjugations, weight
matching or T-unitarity. Prove that the old equal-character positive-dimension
package implies the new local positivity package, so its conjugation adapter
continues to apply. Do not claim that the old conjugation conditions generate
arbitrary unequal indices.

## Steps And Stop Condition

1. Define shared positive support and prove recovery from common virtual index.
2. Extract all three quotients at the same index, without equating characters.
3. Connect to the existing actual-field alternation and exterior construction.
4. Audit unequal signed profiles with nonpositive total dimensions, missing
   shared support, theorem hypotheses and transitive axioms; run full builds,
   layout/link checks and the existing one-generation computational test.

Stop when these endpoints and audits pass. Do not start the separate two-
different-constituent proposal, automatic irreducible normalization, MFV
spurion inputs, a new GUT model or dynamics. Preserve old proofs and pins.
Lean LSP MCP is unavailable in this session; use source inspection and builds.

## Result

All four steps are complete. [Results and boundaries](results.md) map the
new shared-support predicate, recovery lemmas, common quotient extraction and
actual alternating/exterior endpoints. Neither whole-index equality nor
positive total dimension occurs in the new final theorem. Compact continuity,
the actual compatible SM action and three species character equations remain.

Unequal Circle-index controls have shared positive support with Q/up/e total
dimensions -1, 0, -2. Actual continuous difference realizations and split
extraction are checked. A separate control has positive counts in all three
sectors but no common positive coefficient. These are representation-level
controls, not constructed full-GUT models or a classification of all ways
qque might exist.

The scoped endpoint has no remaining obligations. The deferred topics listed
above remain separate; no source/dependency pin or E6 trust boundary changed.

## Verification And Integration

- Focused endpoint build and the persistent audit: passed. The final audit
  is `Physics.StandardModel.Operators.Audit.AuditSharedPositiveQque`.
- 14 new strict transitive axiom checks: passed with only `propext`,
  `Classical.choice`, `Quot.sound`; includes both final endpoints, the old
  hypothesis recovery and the regression controls. The imported earlier
  mathematical audit also passes its 20 checks.
- `lake build`: passed, 5702 jobs. Pre-existing warnings remain; no new
  source warnings. Early control simplification errors were fixed before
  the final passing build, without weakening audits.
- `node tools/layout/check-layout.mjs`: 657 modules; all checks passed.
- `python3 tools/qque/audit_one_generation.py`: 4 exact finite tests passed;
  not proof premises or an end-to-end model check.
- `node tools/docs/check-links.mjs`: 267 Markdown files; no errors.
- `git diff --check`: passed.

Integration target: `master`; Git ancestry records the topic and no-ff merge
commits. Retain the branch and report merged-state verification. Temporary
build logs are not source-controlled.
