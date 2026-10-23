import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsEvenCoordinates
import Physics.FieldTheory.Jets.WeylHiggsEvenValue
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsEvenCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsEvenValue.S_value => Physics.WeylHiggsEvenValue.S_value,
  GUT.WeylHiggsEvenValue.all_scalar_zero => Physics.WeylHiggsEvenValue.all_scalar_zero,
  GUT.WeylHiggsEvenValue.candidate_coordinates => Physics.WeylHiggsEvenValue.candidate_coordinates,
  GUT.WeylHiggsEvenValue.coordinates_zero => Physics.WeylHiggsEvenValue.coordinates_zero
]

assert_compatible GUT.WeylHiggsEvenValue.S_value => Physics.WeylHiggsEvenValue.S_value
assert_compatible GUT.WeylHiggsEvenValue.all_scalar_zero => Physics.WeylHiggsEvenValue.all_scalar_zero
assert_compatible GUT.WeylHiggsEvenValue.candidate_coordinates => Physics.WeylHiggsEvenValue.candidate_coordinates
assert_compatible GUT.WeylHiggsEvenValue.coordinates_zero => Physics.WeylHiggsEvenValue.coordinates_zero
