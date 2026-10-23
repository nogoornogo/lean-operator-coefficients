import Physics.StandardModel.Operators.Support.Decomposition.SMGenerationCauchy
import Physics.StandardModel.Operators.SMCombinedCompactAction
import Math.RepresentationTheory.SU2ExteriorBlocks
import Math.RepresentationTheory.GenerationExteriorBlocks
import Math.LinearAlgebra.TensorDeterminant
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMGenerationCauchy instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMGenerationCauchy.Group => Physics.SMGenerationCauchy.Group,
  GUT.SMGenerationCauchy.actual_lepton => Physics.SMGenerationCauchy.actual_lepton,
  GUT.SMGenerationCauchy.actual_quark => Physics.SMGenerationCauchy.actual_quark,
  GUT.SMGenerationCauchy.color => Physics.SMGenerationCauchy.color,
  GUT.SMGenerationCauchy.colorBasis => Physics.SMGenerationCauchy.colorBasis,
  GUT.SMGenerationCauchy.color_det => Physics.SMGenerationCauchy.color_det,
  GUT.SMGenerationCauchy.color_spin_det => Physics.SMGenerationCauchy.color_spin_det,
  GUT.SMGenerationCauchy.generations => Physics.SMGenerationCauchy.generations,
  GUT.SMGenerationCauchy.inclusion => Physics.SMGenerationCauchy.inclusion,
  GUT.SMGenerationCauchy.inclusion.eq_1 => Physics.SMGenerationCauchy.inclusion.eq_1,
  GUT.SMGenerationCauchy.instAddCommGroupTensorProductComplexColorDoublet => Physics.SMGenerationCauchy.instAddCommGroupTensorProductComplexColorDoublet,
  GUT.SMGenerationCauchy.instAddCommGroupTensorProductComplexColorDoublet_1 => Physics.SMGenerationCauchy.instAddCommGroupTensorProductComplexColorDoublet_1,
  GUT.SMGenerationCauchy.instAddCommGroupTensorProductComplexDoublet_physics => Physics.SMGenerationCauchy.instAddCommGroupTensorProductComplexDoublet_physics,
  GUT.SMGenerationCauchy.lepton => Physics.SMGenerationCauchy.lepton,
  GUT.SMGenerationCauchy.leptonOne => Physics.SMGenerationCauchy.leptonOne,
  GUT.SMGenerationCauchy.leptonTwo => Physics.SMGenerationCauchy.leptonTwo,
  GUT.SMGenerationCauchy.leptonTwo_injective => Physics.SMGenerationCauchy.leptonTwo_injective,
  GUT.SMGenerationCauchy.quark => Physics.SMGenerationCauchy.quark,
  GUT.SMGenerationCauchy.quarkSix => Physics.SMGenerationCauchy.quarkSix,
  GUT.SMGenerationCauchy.quarkSix_injective => Physics.SMGenerationCauchy.quarkSix_injective,
  GUT.SMGenerationCauchy.quarkThree => Physics.SMGenerationCauchy.quarkThree,
  GUT.SMGenerationCauchy.quarkThree_injective => Physics.SMGenerationCauchy.quarkThree_injective,
  GUT.SMGenerationCauchy.reorder => Physics.SMGenerationCauchy.reorder,
  GUT.SMGenerationCauchy.sixBasis => Physics.SMGenerationCauchy.sixBasis,
  GUT.SMGenerationCauchy.spin => Physics.SMGenerationCauchy.spin,
  GUT.SMGenerationCauchy.spinBasis => Physics.SMGenerationCauchy.spinBasis,
  GUT.SMGenerationCauchy.spinProjection => Physics.SMGenerationCauchy.spinProjection,
  GUT.SMGenerationCauchy.spinProjection.eq_1 => Physics.SMGenerationCauchy.spinProjection.eq_1,
  GUT.SMGenerationCauchy.spin_det => Physics.SMGenerationCauchy.spin_det,
  GUT.SMGenerationCauchy.weak => Physics.SMGenerationCauchy.weak,
  GUT.SMGenerationCauchy.weakProjection => Physics.SMGenerationCauchy.weakProjection,
  GUT.SMGenerationCauchy.weakProjection.eq_1 => Physics.SMGenerationCauchy.weakProjection.eq_1,
  GUT.SMMixedCompactWeyl.compact.eq_1 => Physics.SMMixedCompactWeyl.compact.eq_1
]

assert_compatible GUT.SMGenerationCauchy.Group => Physics.SMGenerationCauchy.Group
assert_compatible GUT.SMGenerationCauchy.actual_lepton => Physics.SMGenerationCauchy.actual_lepton
assert_compatible GUT.SMGenerationCauchy.actual_quark => Physics.SMGenerationCauchy.actual_quark
assert_compatible GUT.SMGenerationCauchy.color => Physics.SMGenerationCauchy.color
assert_compatible GUT.SMGenerationCauchy.colorBasis => Physics.SMGenerationCauchy.colorBasis
assert_compatible GUT.SMGenerationCauchy.color_det => Physics.SMGenerationCauchy.color_det
assert_compatible GUT.SMGenerationCauchy.color_spin_det => Physics.SMGenerationCauchy.color_spin_det
assert_compatible GUT.SMGenerationCauchy.generations => Physics.SMGenerationCauchy.generations
assert_compatible GUT.SMGenerationCauchy.inclusion => Physics.SMGenerationCauchy.inclusion
assert_compatible GUT.SMGenerationCauchy.inclusion.eq_1 => Physics.SMGenerationCauchy.inclusion.eq_1
assert_compatible GUT.SMGenerationCauchy.instAddCommGroupTensorProductComplexColorDoublet => Physics.SMGenerationCauchy.instAddCommGroupTensorProductComplexColorDoublet
assert_compatible GUT.SMGenerationCauchy.instAddCommGroupTensorProductComplexColorDoublet_1 => Physics.SMGenerationCauchy.instAddCommGroupTensorProductComplexColorDoublet_1
assert_compatible GUT.SMGenerationCauchy.instAddCommGroupTensorProductComplexDoublet_physics => Physics.SMGenerationCauchy.instAddCommGroupTensorProductComplexDoublet_physics
assert_compatible GUT.SMGenerationCauchy.lepton => Physics.SMGenerationCauchy.lepton
assert_compatible GUT.SMGenerationCauchy.leptonOne => Physics.SMGenerationCauchy.leptonOne
assert_compatible GUT.SMGenerationCauchy.leptonTwo => Physics.SMGenerationCauchy.leptonTwo
assert_compatible GUT.SMGenerationCauchy.leptonTwo_injective => Physics.SMGenerationCauchy.leptonTwo_injective
assert_compatible GUT.SMGenerationCauchy.quark => Physics.SMGenerationCauchy.quark
assert_compatible GUT.SMGenerationCauchy.quarkSix => Physics.SMGenerationCauchy.quarkSix
assert_compatible GUT.SMGenerationCauchy.quarkSix_injective => Physics.SMGenerationCauchy.quarkSix_injective
assert_compatible GUT.SMGenerationCauchy.quarkThree => Physics.SMGenerationCauchy.quarkThree
assert_compatible GUT.SMGenerationCauchy.quarkThree_injective => Physics.SMGenerationCauchy.quarkThree_injective
assert_compatible GUT.SMGenerationCauchy.reorder => Physics.SMGenerationCauchy.reorder
assert_compatible GUT.SMGenerationCauchy.sixBasis => Physics.SMGenerationCauchy.sixBasis
assert_compatible GUT.SMGenerationCauchy.spin => Physics.SMGenerationCauchy.spin
assert_compatible GUT.SMGenerationCauchy.spinBasis => Physics.SMGenerationCauchy.spinBasis
assert_compatible GUT.SMGenerationCauchy.spinProjection => Physics.SMGenerationCauchy.spinProjection
assert_compatible GUT.SMGenerationCauchy.spinProjection.eq_1 => Physics.SMGenerationCauchy.spinProjection.eq_1
assert_compatible GUT.SMGenerationCauchy.spin_det => Physics.SMGenerationCauchy.spin_det
assert_compatible GUT.SMGenerationCauchy.weak => Physics.SMGenerationCauchy.weak
assert_compatible GUT.SMGenerationCauchy.weakProjection => Physics.SMGenerationCauchy.weakProjection
assert_compatible GUT.SMGenerationCauchy.weakProjection.eq_1 => Physics.SMGenerationCauchy.weakProjection.eq_1
assert_compatible GUT.SMMixedCompactWeyl.compact.eq_1 => Physics.SMMixedCompactWeyl.compact.eq_1
