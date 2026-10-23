# Resumed Foundation Checkpoint

This records an intermediate checkpoint. Its pending tasks are now discharged
by the [completed result](results.md); its check counts remain checkpoint evidence.

The [resumed contract](completeness-plan.md) remains active. This checkpoint
does not assert the coefficient equivalence or conclude the topic.

## Proved full-source interfaces

- [First-jet words](../../../Math/Algebra/MixedFirstJetWords.lean) span the
  entire mixed grade of derivative order one. The theorem marks one slot
  among all odd and even factors, retaining arbitrary field labels.
- [Two-sided normal form](../../../Math/Algebra/TwoSidedDifferentialNormalForm.lean)
  expresses the full differential equation closure as the linear span of
  arbitrary left/right multiples of all iterated seed derivatives. It
  assumes the even Leibniz rule and imposes no truncation.
- [Odd projection](../../../Math/Algebra/MixedJetConstantOdd.lean) removes
  positive odd jets in an exterior algebra. It preserves the fermionic
  algebra and sends every odd total derivative to zero.
- [Mixed wave evaluation](../../../Math/Algebra/MixedFourWaveEvaluation.lean)
  combines that projection with the existing colored four-wave evaluation.
  Kernel stability proves annihilation of the entire two-sided differential
  closure, and conserving momenta kill the whole linear divergence range.

## C5 consequence

[Weyl/Higgs waves](../../../Physics/FieldTheory/Jets/WeylHiggsWaves.lean)
annihilate all actual free C5 relations for arbitrary null momentum, both
color indices and either ordered left/right spinor probe. Generated and
component equations are connected through the checked full closure equality.

[Wave values](../../../Physics/FieldTheory/Jets/WeylHiggsWaveValues.lean)
give the exact candidate value for this family. The null vector (1,0,0,1)
and the zero color/spinor indices give 16i. Consequently the current
candidate is nonzero modulo the full EOM/IBP relation module. This improves
the earlier raw probe, which did not kill IBP.

An individual wave probe is not asserted to be group invariant. A nonzero
EOM/IBP class and the density's existing invariance do not by themselves
prove nonzero invariant dual coefficients. The arbitrary-group invariant
lower functional and upper uniqueness remain the next required work.

## Verification

Focused source and strict audit builds pass. The fresh Math inventory checks
10 first-word, 19 mixed-wave, 7 odd-projection and 38 complete two-sided
namespace declarations; the Physics inventory checks 24 wave and 13 wave-value
declarations. All 111 checks permit only propext, Classical.choice and
Quot.sound transitively, with the original import-layer restrictions.

The serialized full `lake build` passes 7967 jobs at the recorded resource
limits. New sources have no tactic/linter warnings; the direct mathlib
imports retain the module-system advisories used by the existing sources.
The whole coefficient equivalence and its literature comparison are pending.
