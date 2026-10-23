import Physics.StandardModel.Gauge.Tensors.SMEpsilonTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.SMEpsilonTensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMEpsilonTensor.Color => Physics.SMEpsilonTensor.Color,
  GUT.SMEpsilonTensor.Weak => Physics.SMEpsilonTensor.Weak,
  GUT.SMEpsilonTensor.colorBasis => Physics.SMEpsilonTensor.colorBasis,
  GUT.SMEpsilonTensor.colorBasis.eq_1 => Physics.SMEpsilonTensor.colorBasis.eq_1,
  GUT.SMEpsilonTensor.colorTensor => Physics.SMEpsilonTensor.colorTensor,
  GUT.SMEpsilonTensor.colorTensor_tmul => Physics.SMEpsilonTensor.colorTensor_tmul,
  GUT.SMEpsilonTensor.eps2 => Physics.SMEpsilonTensor.eps2,
  GUT.SMEpsilonTensor.eps2.eq_1 => Physics.SMEpsilonTensor.eps2.eq_1,
  GUT.SMEpsilonTensor.eps2Bilin => Physics.SMEpsilonTensor.eps2Bilin,
  GUT.SMEpsilonTensor.eps2_basis => Physics.SMEpsilonTensor.eps2_basis,
  GUT.SMEpsilonTensor.eps2_det => Physics.SMEpsilonTensor.eps2_det,
  GUT.SMEpsilonTensor.eps2_invariant => Physics.SMEpsilonTensor.eps2_invariant,
  GUT.SMEpsilonTensor.eps2_smul_left => Physics.SMEpsilonTensor.eps2_smul_left,
  GUT.SMEpsilonTensor.eps2_smul_right => Physics.SMEpsilonTensor.eps2_smul_right,
  GUT.SMEpsilonTensor.eps3 => Physics.SMEpsilonTensor.eps3,
  GUT.SMEpsilonTensor.eps3.eq_1 => Physics.SMEpsilonTensor.eps3.eq_1,
  GUT.SMEpsilonTensor.eps3Trilin => Physics.SMEpsilonTensor.eps3Trilin,
  GUT.SMEpsilonTensor.eps3_basis => Physics.SMEpsilonTensor.eps3_basis,
  GUT.SMEpsilonTensor.eps3_det => Physics.SMEpsilonTensor.eps3_det,
  GUT.SMEpsilonTensor.eps3_invariant => Physics.SMEpsilonTensor.eps3_invariant,
  GUT.SMEpsilonTensor.eps3_smul_first => Physics.SMEpsilonTensor.eps3_smul_first,
  GUT.SMEpsilonTensor.eps3_smul_second => Physics.SMEpsilonTensor.eps3_smul_second,
  GUT.SMEpsilonTensor.eps3_smul_third => Physics.SMEpsilonTensor.eps3_smul_third,
  GUT.SMEpsilonTensor.weakBasis => Physics.SMEpsilonTensor.weakBasis,
  GUT.SMEpsilonTensor.weakBasis.eq_1 => Physics.SMEpsilonTensor.weakBasis.eq_1,
  GUT.SMEpsilonTensor.weakTensor => Physics.SMEpsilonTensor.weakTensor,
  GUT.SMEpsilonTensor.weakTensor_tmul => Physics.SMEpsilonTensor.weakTensor_tmul
]

assert_compatible GUT.SMEpsilonTensor.Color => Physics.SMEpsilonTensor.Color
assert_compatible GUT.SMEpsilonTensor.Weak => Physics.SMEpsilonTensor.Weak
assert_compatible GUT.SMEpsilonTensor.colorBasis => Physics.SMEpsilonTensor.colorBasis
assert_compatible GUT.SMEpsilonTensor.colorBasis.eq_1 => Physics.SMEpsilonTensor.colorBasis.eq_1
assert_compatible GUT.SMEpsilonTensor.colorTensor => Physics.SMEpsilonTensor.colorTensor
assert_compatible GUT.SMEpsilonTensor.colorTensor_tmul => Physics.SMEpsilonTensor.colorTensor_tmul
assert_compatible GUT.SMEpsilonTensor.eps2 => Physics.SMEpsilonTensor.eps2
assert_compatible GUT.SMEpsilonTensor.eps2.eq_1 => Physics.SMEpsilonTensor.eps2.eq_1
assert_compatible GUT.SMEpsilonTensor.eps2Bilin => Physics.SMEpsilonTensor.eps2Bilin
assert_compatible GUT.SMEpsilonTensor.eps2_basis => Physics.SMEpsilonTensor.eps2_basis
assert_compatible GUT.SMEpsilonTensor.eps2_det => Physics.SMEpsilonTensor.eps2_det
assert_compatible GUT.SMEpsilonTensor.eps2_invariant => Physics.SMEpsilonTensor.eps2_invariant
assert_compatible GUT.SMEpsilonTensor.eps2_smul_left => Physics.SMEpsilonTensor.eps2_smul_left
assert_compatible GUT.SMEpsilonTensor.eps2_smul_right => Physics.SMEpsilonTensor.eps2_smul_right
assert_compatible GUT.SMEpsilonTensor.eps3 => Physics.SMEpsilonTensor.eps3
assert_compatible GUT.SMEpsilonTensor.eps3.eq_1 => Physics.SMEpsilonTensor.eps3.eq_1
assert_compatible GUT.SMEpsilonTensor.eps3Trilin => Physics.SMEpsilonTensor.eps3Trilin
assert_compatible GUT.SMEpsilonTensor.eps3_basis => Physics.SMEpsilonTensor.eps3_basis
assert_compatible GUT.SMEpsilonTensor.eps3_det => Physics.SMEpsilonTensor.eps3_det
assert_compatible GUT.SMEpsilonTensor.eps3_invariant => Physics.SMEpsilonTensor.eps3_invariant
assert_compatible GUT.SMEpsilonTensor.eps3_smul_first => Physics.SMEpsilonTensor.eps3_smul_first
assert_compatible GUT.SMEpsilonTensor.eps3_smul_second => Physics.SMEpsilonTensor.eps3_smul_second
assert_compatible GUT.SMEpsilonTensor.eps3_smul_third => Physics.SMEpsilonTensor.eps3_smul_third
assert_compatible GUT.SMEpsilonTensor.weakBasis => Physics.SMEpsilonTensor.weakBasis
assert_compatible GUT.SMEpsilonTensor.weakBasis.eq_1 => Physics.SMEpsilonTensor.weakBasis.eq_1
assert_compatible GUT.SMEpsilonTensor.weakTensor => Physics.SMEpsilonTensor.weakTensor
assert_compatible GUT.SMEpsilonTensor.weakTensor_tmul => Physics.SMEpsilonTensor.weakTensor_tmul
