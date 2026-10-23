import Physics.StandardModel.Operators.Support.Lepton.SMLeptonCoreBranching
import Math.RepresentationTheory.SU2PairExterior
import Math.RepresentationTheory.SU2PairGenerationSupport
import Math.RepresentationTheory.SU2PairGenerationBounds
import Physics.StandardModel.Operators.SMGenerationCauchy
import Physics.StandardModel.Operators.SMGenerationExhaustion
import Physics.StandardModel.Operators.SMGenerationCoefficients
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Lepton.SMLeptonCoreBranching instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMGenerationExhaustion.core.eq_1 => Physics.SMGenerationExhaustion.core.eq_1,
  GUT.SMLeptonCoreBranching.actual_core => Physics.SMLeptonCoreBranching.actual_core,
  GUT.SMLeptonCoreBranching.actual_field => Physics.SMLeptonCoreBranching.actual_field,
  GUT.SMLeptonCoreBranching.core => Physics.SMLeptonCoreBranching.core,
  GUT.SMLeptonCoreBranching.exteriorEquiv => Physics.SMLeptonCoreBranching.exteriorEquiv,
  GUT.SMLeptonCoreBranching.field => Physics.SMLeptonCoreBranching.field,
  GUT.SMLeptonCoreBranching.fieldExteriorEquiv => Physics.SMLeptonCoreBranching.fieldExteriorEquiv,
  GUT.SMLeptonCoreBranching.generation_bounds_iff => Physics.SMLeptonCoreBranching.generation_bounds_iff,
  GUT.SMLeptonCoreBranching.generation_forbidden_iff => Physics.SMLeptonCoreBranching.generation_forbidden_iff,
  GUT.SMLeptonCoreBranching.generation_target_iff => Physics.SMLeptonCoreBranching.generation_target_iff,
  GUT.SMLeptonCoreBranching.instAddCommGroupPairCarrier_physics => Physics.SMLeptonCoreBranching.instAddCommGroupPairCarrier_physics,
  GUT.SMLeptonCoreBranching.instAddCommGroupTensorProductComplexDoubletForallFinOfNatNat_physics => Physics.SMLeptonCoreBranching.instAddCommGroupTensorProductComplexDoubletForallFinOfNatNat_physics,
  GUT.SMLeptonCoreBranching.instAddCommGroupTensorProductComplexDoublet_physics => Physics.SMLeptonCoreBranching.instAddCommGroupTensorProductComplexDoublet_physics,
  GUT.SMLeptonCoreBranching.projection => Physics.SMLeptonCoreBranching.projection,
  GUT.SMLeptonCoreBranching.projection.eq_1 => Physics.SMLeptonCoreBranching.projection.eq_1,
  GUT.SMLeptonCoreBranching.projection_surjective => Physics.SMLeptonCoreBranching.projection_surjective,
  GUT.SMLeptonCoreBranching.source_target_iff => Physics.SMLeptonCoreBranching.source_target_iff,
  GUT.SMLeptonCoreBranching.target_iff => Physics.SMLeptonCoreBranching.target_iff
]

assert_compatible GUT.SMGenerationExhaustion.core.eq_1 => Physics.SMGenerationExhaustion.core.eq_1
assert_compatible GUT.SMLeptonCoreBranching.actual_core => Physics.SMLeptonCoreBranching.actual_core
assert_compatible GUT.SMLeptonCoreBranching.actual_field => Physics.SMLeptonCoreBranching.actual_field
assert_compatible GUT.SMLeptonCoreBranching.core => Physics.SMLeptonCoreBranching.core
assert_compatible GUT.SMLeptonCoreBranching.exteriorEquiv => Physics.SMLeptonCoreBranching.exteriorEquiv
assert_compatible GUT.SMLeptonCoreBranching.field => Physics.SMLeptonCoreBranching.field
assert_compatible GUT.SMLeptonCoreBranching.fieldExteriorEquiv => Physics.SMLeptonCoreBranching.fieldExteriorEquiv
assert_compatible GUT.SMLeptonCoreBranching.generation_bounds_iff => Physics.SMLeptonCoreBranching.generation_bounds_iff
assert_compatible GUT.SMLeptonCoreBranching.generation_forbidden_iff => Physics.SMLeptonCoreBranching.generation_forbidden_iff
assert_compatible GUT.SMLeptonCoreBranching.generation_target_iff => Physics.SMLeptonCoreBranching.generation_target_iff
assert_compatible GUT.SMLeptonCoreBranching.instAddCommGroupPairCarrier_physics => Physics.SMLeptonCoreBranching.instAddCommGroupPairCarrier_physics
assert_compatible GUT.SMLeptonCoreBranching.instAddCommGroupTensorProductComplexDoubletForallFinOfNatNat_physics => Physics.SMLeptonCoreBranching.instAddCommGroupTensorProductComplexDoubletForallFinOfNatNat_physics
assert_compatible GUT.SMLeptonCoreBranching.instAddCommGroupTensorProductComplexDoublet_physics => Physics.SMLeptonCoreBranching.instAddCommGroupTensorProductComplexDoublet_physics
assert_compatible GUT.SMLeptonCoreBranching.projection => Physics.SMLeptonCoreBranching.projection
assert_compatible GUT.SMLeptonCoreBranching.projection.eq_1 => Physics.SMLeptonCoreBranching.projection.eq_1
assert_compatible GUT.SMLeptonCoreBranching.projection_surjective => Physics.SMLeptonCoreBranching.projection_surjective
assert_compatible GUT.SMLeptonCoreBranching.source_target_iff => Physics.SMLeptonCoreBranching.source_target_iff
assert_compatible GUT.SMLeptonCoreBranching.target_iff => Physics.SMLeptonCoreBranching.target_iff
