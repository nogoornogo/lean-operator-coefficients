# Partial Target: Checked Results

The [topic plan](README.md) is complete. The current statement and limits are
in the [structural criterion](../../proof/current/inputs/Physics/STRUCTURAL_CONJUGATION.md).

## PT-1: Actual Coefficient Invariance

Commit `checkpoint 01` adds
[CoefficientTransport](../../../Math/RepresentationTheory/Characters/CoefficientTransport.lean)
and [ConjugationDualIndex](../../../Physics/StandardModel/Spectrum/ConjugationDualIndex.lean).

`AbelianActualSpectrum.coeff_comp_eq_of_eval_invariant` transports coefficients
of finite scalar-character polynomials under a group automorphism, using
faithful evaluation. The Physics bridge applies this to the actual radical's
dual spectrum. Mass conservation equates its evaluation with the source dual
trace; actual ambient conjugation then supplies evaluation invariance.
`ConjugationDualIndex.coeff_permute` obtains equality at permuted integral keys.

No full target, global Laurent polynomiality, or invariant action of the
conjugating elements on the radical is assumed. The full finite polynomial
uses all actual scalar characters, including any outside the integral-key image.

Persistent audit: 7 strict transitive checks, focused build 3820 jobs. Full
regression: 5570 jobs; layout: 554 modules.

## PT-2: Local Matching And The Endpoint

Commit `checkpoint 02` adds
[SMPartialTarget](../../../Physics/StandardModel/Spectrum/SMPartialTarget.lean)
and [ConjugationPartialTarget](../../../Physics/StandardModel/Spectrum/ConjugationPartialTarget.lean).

`HasPartialTarget` fixes the actual radical dual-index coefficients only at
the fifteen oriented SM weights, for all residual characters. It does not
fix coefficients at other weights. The finite nonnegative profiles have
separate positive Q/down totals. Ambient unitarity remains unnecessary.

The three unchanged actual conjugations derive `profiles_compatible` from
these local coefficients. Nonnegativity of the actual opposite coefficients
then yields positive radical multiplicities and nonzero joint eigenvectors.
`exists_actual_signature_pair` and `selection_rule_obstruction` give the same
`qque`/`duql` endpoint on the original actual resolved spectrum.

`of_full_target` proves the previous full target implies the local condition.
The persistent audit also checks actual ambient-field vectors satisfying the
zero-mass equation and a full-target consumer using the new theorem.
No prior API, proof or model was removed.

Persistent audit: 15 strict transitive checks, focused build 3822 jobs. Full
regression: 5573 jobs; layout: 557 modules.

## PT-3: Extra-Sector Boundary Controls

[AuditPartialTargetExtras](../../../Physics/StandardModel/Spectrum/Audit/AuditPartialTargetExtras.lean)
uses the finite additive charge group `ZMod 3`. These are coefficient-algebra
controls, not actual GUT models or new anomaly-cancellation results.

- `add_of_dual_vanishes` preserves local matching when an added finite sector
  has zero dual contribution at every monitored weight and charge.
- At the reduced weight `(10,10,10,10)`, one additional neutral component has
  nonzero dual index. It preserves local matching for any target profiles,
  but `with_extra_not_full_target` shows it cannot equal a full target with
  those profiles, even after arbitrary singlets are added.
- A component at the negative of the first SM weight has zero coefficient at
  every positive SM weight but changes the dual coefficient. Lean proves this
  breaks matching (`contaminant_breaks_matching`). This guards against ignoring
  opposite weights when admitting extra sectors.

The positive example separates the two matching predicates at the coefficient
level. It does not prove that this isolated exotic component extends to matter
admitting all ambient conjugations. Unmonitored coefficients still obey those
representation/conjugation constraints; they are not freely assignable.

Focused extra-sector audit: 3084 jobs, 6 strict transitive checks. Across PT-1
through PT-3 there are 28 new strict checks, allowing only `propext`,
`Classical.choice`, `Quot.sound`, with Physics/GUT import-boundary checks.

## Final Verification And Limits

- Full `lake build`: passed, 5574 jobs.
- `node tools/layout/check-layout.mjs`: passed, 558 modules.
- Documentation links and `git diff --check`: checked before integration.
- Existing finite-basis unused-section-variable warnings remain; new modules
  emit no warnings. Dependency pins and existing source interfaces are unchanged.
- No new literature inputs, external proof oracles, custom axioms or placeholders.

All three approved assumption relaxations now hold simultaneously. Finite
dimensionality, the fixed SM coordinates, actual conjugations, Abelian residual
symmetry, restricted unitarity, invariant symmetric mass, local positive-index
matching and positive Q/down totals remain. Minimality is not established.
There is no new claim of anomaly consistency, full-gauge/Lorentz/Grassmann
nonvanishing, generated coefficients, amplitudes, or finite proton lifetime.
The E6 literature boundary is unchanged.
