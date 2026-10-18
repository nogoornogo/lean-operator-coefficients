# SC-4: Actual Triality Negative Control

Status: completed. The [topic](README.md) owns integration and the frozen scope.

## Checked Result

[ConjugationTrialityObstruction](../../../Physics/StandardModel/Spectrum/ConjugationTrialityObstruction.lean)
proves that the lepton-triality profiles fail the down/lepton equality forced
by the three conjugations. It supplies three versions of the obstruction:

- The actual source dual character cannot match the triality target while all
  three conjugations exist (`no_conjugations_of_dual_target`).
- The same holds for an invariant symmetric mass with only the exact dual
  light target (`no_conjugations_of_light_target`). This does not impose equality
  of full spectra or absence of additional vectorlike modes.
- An ambient representation matching the actual 45-dimensional triality
  source character on physical torus/residual coordinates cannot have all
  three witnesses (`no_conjugations_of_actual_source_character`). In particular,
  an extension on the same fields preserving the actual action cannot have
  them (`no_actual_extension`).

The physical coordinates cover the chosen determinant-one torus. The actual
source character is identified using its zero-mass radical equivalence, not
an assumed abstract spectrum. This does not prohibit embedding the torus
alone in a larger group.

## Audit And Regression

[Persistent audit](../../../Physics/StandardModel/Spectrum/Audit/AuditConjugationTrialityObstruction.lean):
7 strict transitive axiom checks, allowing only `propext`, `Classical.choice`
and `Quot.sound`; general Physics imports no GUT application modules. A consumer
also checks the existing radical dimension 45, actual supported charges and
universal prohibition in the specified signature class.

- Focused audit: passed (3873 jobs).
- Full `lake build`: passed (5564 jobs).
- `node tools/layout/check-layout.mjs`: passed, 548 modules.
- Documentation links and `git diff --check`: checked at integration.
- Existing finite-basis unused-section-variable warnings remain; no new warnings.

Together with the actual SU(5)-chain positive control, this closes SC-4. Neither
quantum anomaly cancellation for triality nor a new class of physical models
satisfying the sufficient criterion is claimed.
