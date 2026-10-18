# Two Conjugations For QQue

- ID: two-conjugation-qque
- Status: completed
- Working branch: `proof/two-conjugation-qque`
- Integration target: `master`; user authorized merging after verification
- Result type: two witnesses suffice for the original supported pair and finite
  non-Abelian internal coefficient pair; Q-only qque endpoints also checked

## Frozen Goal

Replace the three actual ambient conjugations by the Q/up and Q/electron
conjugations for a qque-only endpoint. Retain finite-dimensional actual matter,
restricted unitarity, invariant symmetric mass, local positive SM dual targets,
strict commuting residual action and actual light support. The minimum goal
is qque alone; see the checked refinement below for retained duql conclusions.
Do not identify additional physical embeddings without separate work.

Preserve the existing stronger three-conjugation theorems. Supply the
three-to-two adapter and the finite non-Abelian ordered internal qque endpoint
as well as the Abelian supported-signature result. Keep their different
conclusion types and physical boundaries explicit.

## Support Gate And Checked Refinement

The legacy `ChargesSupported` checks all five species, including down/lepton
which do not occur in qque. Initially we planned to treat their occupancy
independently. Inspection instead found and Lean checked that `(3 1)` also
sends SM weight 10 (down) to weight 13 (lepton). With the retained all-fifteen
species-uniform target, the two moves therefore suffice for down/lepton
compatibility as well. No third conjugator is constructed or assumed.

Bounded refinement: prove the unchanged full-support pair and old obstruction
from two moves, with the original positive Q/down totals. This reuses the same
finite coefficient argument; no physical assumptions or new foundations are added.
Keep the qque-only path too, since it needs positive Q only:

- Add explicit operator-slot support, requiring actual sectors only for fields
  appearing in that operator. Do not weaken any old definition in place.
- Derive the qque-only obstruction with positive Q target, without requiring
  down/lepton positivity or their character equality.
- Recover the exact legacy full-support conclusion with positive Q/down totals;
  lepton positivity is derived using the additional checked weight relation.
- Audit the distinction: a missing spectator species makes the old universal
  prohibition predicate vacuous, not a counterexample to the new endpoint.

## Work Packages And Stop Condition

| ID | Deliverable | State |
| --- | --- | --- |
| TC-1 | Two actual conjugations and three-to-two adapter; Q/up/e relations | Proved |
| TC-2 | Actual supported Abelian qque, slotwise obstruction and unchanged full-support pair | Proved |
| TC-3 | Finite non-Abelian actual light coefficients from two conjugations | Proved, including the pair with positive down target |
| TC-4 | Strict audits, scope documentation, regression and integration | Checks passed; integration authorized, recorded by Git ancestry |

Stop when these endpoints and controls pass, or a genuine obstruction requires
a scope decision. No new embeddings, infinite non-Abelian theory, full-gauge
radical tensor lift, Lorentz/Grassmann nonvanishing, dynamics or E6 foundations.
No dependency changes, new axioms or `sorry`. All bounded deliverables are
closed. Minimality and strictly larger physical model coverage remain unclaimed.
See [the precise result](../../proof/current/inputs/Physics/TWO_CONJUGATIONS.md).

## Verification

Checkpoint stage 01:

- Three focused persistent audits: 25 strict declaration checks (5 + 12 + 8),
  allowing only `propext`, `Classical.choice`, `Quot.sound` transitively.
- The negative `triality_no_two` control passes; full-to-slot support and
  the legacy no-lepton vacuity control pass. Old declarations remain intact.
- `lake build`: 5615 jobs passed, including old application/adapter audits.
- Layout: 594 modules; layers, cycles and aggregates passed.
- Documentation: 241 Markdown files, 32 fragments, zero link errors.
- `git diff --check`: passed. New modules are warning-free; existing warnings replay.
- New finite-group endpoint builds took about 79-97 seconds; local heartbeat
  allowances match the existing actual-subspace tensor endpoints.

Merge with `--no-ff`, recheck the merged tree and retain this branch. No remote push.

## Sources

- [Actual conjugations](../../../Physics/StandardModel/Spectrum/ConjugationSource.lean)
- [Abelian local source](../../../Physics/StandardModel/Spectrum/ConjugationPartialTarget.lean)
- [Legacy supported operators](../../../Physics/StandardModel/Operators/StandardModelLocalOperator.lean)
- [Finite non-Abelian source](../../../Physics/StandardModel/Spectrum/NonabelianLightSource.lean)
- [Finite non-Abelian endpoint](../../../Physics/StandardModel/Operators/NonabelianLightOperators.lean)
