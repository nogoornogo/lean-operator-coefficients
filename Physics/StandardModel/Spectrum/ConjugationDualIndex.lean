import Physics.StandardModel.Spectrum.Representations.ConjugationDualIndex
import Physics.StandardModel.Spectrum.RestrictedConjugationMassSource
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.ConjugationDualIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ConjugationDualIndex.coeff_permute => Physics.ConjugationDualIndex.coeff_permute,
  GUT.ConjugationDualIndex.coordinateEquiv => Physics.ConjugationDualIndex.coordinateEquiv,
  GUT.ConjugationDualIndex.dualIndex => Physics.ConjugationDualIndex.dualIndex,
  GUT.ConjugationDualIndex.dualIndex.eq_1 => Physics.ConjugationDualIndex.dualIndex.eq_1,
  GUT.ConjugationDualIndex.dualIndex_apply => Physics.ConjugationDualIndex.dualIndex_apply,
  GUT.ConjugationDualIndex.fullDual_eval => Physics.ConjugationDualIndex.fullDual_eval,
  GUT.ConjugationDualIndex.keyCharacter_permute => Physics.ConjugationDualIndex.keyCharacter_permute
]

assert_compatible GUT.ConjugationDualIndex.coeff_permute => Physics.ConjugationDualIndex.coeff_permute
assert_compatible GUT.ConjugationDualIndex.coordinateEquiv => Physics.ConjugationDualIndex.coordinateEquiv
assert_compatible GUT.ConjugationDualIndex.dualIndex => Physics.ConjugationDualIndex.dualIndex
assert_compatible GUT.ConjugationDualIndex.dualIndex.eq_1 => Physics.ConjugationDualIndex.dualIndex.eq_1
assert_compatible GUT.ConjugationDualIndex.dualIndex_apply => Physics.ConjugationDualIndex.dualIndex_apply
assert_compatible GUT.ConjugationDualIndex.fullDual_eval => Physics.ConjugationDualIndex.fullDual_eval
assert_compatible GUT.ConjugationDualIndex.keyCharacter_permute => Physics.ConjugationDualIndex.keyCharacter_permute
