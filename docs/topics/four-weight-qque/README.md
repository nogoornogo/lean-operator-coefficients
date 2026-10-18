# Four-Weight QQue

- ID: four-weight-qque
- Status: completed
- Result type: proved in both routes; qque-only endpoint
- Working branch: `proof/four-weight-qque`
- Integration target: `master`; user authorizes merge on completion

## Frozen Goal

For Abelian profiles and finite non-Abelian representation targets, require
local dual-index matching only at weights 0, 3, 8, 14. Preserve two actual
conjugations, finite-dimensional actual matter, the existing restricted
unitarity assumptions, invariant symmetric mass, and nonzero Q target.
Derive actual supported neutral qque (Abelian) and a nonzero ordered internal
qque coefficient on actual light sectors (finite non-Abelian).

The opposite-weight dual contribution is retained. The two Q slots use the
same Q target. Do not assume cross-species compatibility, projections or
nonzero coefficients. Reuse existing five-species data containers; unused
down/lepton entries must impose no matching/positivity condition.

## Deliverables And Stop Gate

1. Four-weight predicates and adapters from both existing fifteen-weight targets.
2. Abelian profile compatibility, actual slot support and qque obstruction.
3. Finite non-Abelian common light quotient, qque coefficient and obstruction.
4. Persistent strict audits, controls for target weakening/support, focused and
   full builds, documentation, commit and `--no-ff` integration.

Stop when these pass. Do not claim duql, minimality, new physical models,
full-gauge/Lorentz/Grassmann nonvanishing, compact infinite H or amplitudes.
No changes to dependency pins, old statements or axiom allowlists.

## Verification

Checkpoint stage 01:

- Focused build of `AuditFourWeightQque` and `AuditFourWeightLightQque`:
  3906 jobs passed, 20 strict transitive checks (13 + 7; including the retained
  qque slot-neutrality theorem). Only `propext`, `Classical.choice`, `Quot.sound`.
- `lake build`: 5620 jobs passed, including existing proof/audit regressions.
- Layout checker: 599 modules; layers, local imports, cycles and aggregate
  coverage passed.
- Documentation checker: 244 Markdown files, zero errors.
- `git diff --check`: passed. New modules have no warnings; old warnings replay.
- No `sorry`, custom axioms, dependency changes or old theorem modifications.
- Lean LSP MCP unavailable; source inspection and Lake builds used.

## Results And Boundaries

All deliverables are closed. [The proof dossier](../../proof/current/applications/Physics/FOUR_WEIGHT_QQUE.md)
records both source adapters and actual-light endpoints. Positive Q is retained;
common charges/irreducible quotients and nonzero coefficients are derived.
Controls show strictness at the profile-predicate level, failure of a positive
target on a zero spectrum, and exclusion of triality already at four weights.
Unused target entries are proved irrelevant to matching in both routes.

No new physical model or minimality theorem is claimed. The existing duql/pair
theorems keep their fifteen-weight inputs. Commit and merge into master after
checks; recheck the merged result and retain this branch. Git ancestry records
integration; no remote push.
