import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsEvenValue
import Physics.FieldTheory.Jets.WeylHiggsInternalIBP
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsEvenValue instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsEvenValue.S => Physics.WeylHiggsEvenValue.S,
  GUT.WeylHiggsEvenValue.S.eq_1 => Physics.WeylHiggsEvenValue.S.eq_1,
  GUT.WeylHiggsEvenValue.candidate_sum => Physics.WeylHiggsEvenValue.candidate_sum,
  GUT.WeylHiggsEvenValue.candidate_value_raw => Physics.WeylHiggsEvenValue.candidate_value_raw,
  GUT.WeylHiggsEvenValue.current_radius => Physics.WeylHiggsEvenValue.current_radius,
  GUT.WeylHiggsEvenValue.current_value => Physics.WeylHiggsEvenValue.current_value,
  GUT.WeylHiggsEvenValue.even_value => Physics.WeylHiggsEvenValue.even_value,
  GUT.WeylHiggsEvenValue.instAddCommGroupA_physics => Physics.WeylHiggsEvenValue.instAddCommGroupA_physics,
  GUT.WeylHiggsEvenValue.instModuleComplexA_physics => Physics.WeylHiggsEvenValue.instModuleComplexA_physics,
  GUT.WeylHiggsEvenValue.instRingA_physics => Physics.WeylHiggsEvenValue.instRingA_physics,
  GUT.WeylHiggsEvenValue.kernel_trace => Physics.WeylHiggsEvenValue.kernel_trace,
  GUT.WeylHiggsEvenValue.minus => Physics.WeylHiggsEvenValue.minus,
  GUT.WeylHiggsEvenValue.minus.eq_1 => Physics.WeylHiggsEvenValue.minus.eq_1,
  GUT.WeylHiggsEvenValue.plus => Physics.WeylHiggsEvenValue.plus,
  GUT.WeylHiggsEvenValue.plus.eq_1 => Physics.WeylHiggsEvenValue.plus.eq_1,
  GUT.WeylHiggsEvenValue.scalarMono => Physics.WeylHiggsEvenValue.scalarMono,
  GUT.WeylHiggsEvenValue.scalarMono.eq_1 => Physics.WeylHiggsEvenValue.scalarMono.eq_1,
  GUT.WeylHiggsEvenValue.spin_trace => Physics.WeylHiggsEvenValue.spin_trace
]

assert_compatible GUT.WeylHiggsEvenValue.S => Physics.WeylHiggsEvenValue.S
assert_compatible GUT.WeylHiggsEvenValue.S.eq_1 => Physics.WeylHiggsEvenValue.S.eq_1
assert_compatible GUT.WeylHiggsEvenValue.candidate_sum => Physics.WeylHiggsEvenValue.candidate_sum
assert_compatible GUT.WeylHiggsEvenValue.candidate_value_raw => Physics.WeylHiggsEvenValue.candidate_value_raw
assert_compatible GUT.WeylHiggsEvenValue.current_radius => Physics.WeylHiggsEvenValue.current_radius
assert_compatible GUT.WeylHiggsEvenValue.current_value => Physics.WeylHiggsEvenValue.current_value
assert_compatible GUT.WeylHiggsEvenValue.even_value => Physics.WeylHiggsEvenValue.even_value
assert_compatible GUT.WeylHiggsEvenValue.instAddCommGroupA_physics => Physics.WeylHiggsEvenValue.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsEvenValue.instModuleComplexA_physics => Physics.WeylHiggsEvenValue.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsEvenValue.instRingA_physics => Physics.WeylHiggsEvenValue.instRingA_physics
assert_compatible GUT.WeylHiggsEvenValue.kernel_trace => Physics.WeylHiggsEvenValue.kernel_trace
assert_compatible GUT.WeylHiggsEvenValue.minus => Physics.WeylHiggsEvenValue.minus
assert_compatible GUT.WeylHiggsEvenValue.minus.eq_1 => Physics.WeylHiggsEvenValue.minus.eq_1
assert_compatible GUT.WeylHiggsEvenValue.plus => Physics.WeylHiggsEvenValue.plus
assert_compatible GUT.WeylHiggsEvenValue.plus.eq_1 => Physics.WeylHiggsEvenValue.plus.eq_1
assert_compatible GUT.WeylHiggsEvenValue.scalarMono => Physics.WeylHiggsEvenValue.scalarMono
assert_compatible GUT.WeylHiggsEvenValue.scalarMono.eq_1 => Physics.WeylHiggsEvenValue.scalarMono.eq_1
assert_compatible GUT.WeylHiggsEvenValue.spin_trace => Physics.WeylHiggsEvenValue.spin_trace
