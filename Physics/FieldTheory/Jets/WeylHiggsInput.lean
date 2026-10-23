import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInput
import Physics.FieldTheory.Jets.WeylCurrentCovariance
import Physics.FieldTheory.Jets.HiggsStandardInput
import Math.Algebra.MixedScalarInclusion
import Math.RepresentationTheory.JetGradeAction
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsInput.Group => Physics.WeylHiggsInput.Group,
  GUT.WeylHiggsInput.V => Physics.WeylHiggsInput.V,
  GUT.WeylHiggsInput.action => Physics.WeylHiggsInput.action,
  GUT.WeylHiggsInput.bosons => Physics.WeylHiggsInput.bosons,
  GUT.WeylHiggsInput.charge => Physics.WeylHiggsInput.charge,
  GUT.WeylHiggsInput.charged => Physics.WeylHiggsInput.charged,
  GUT.WeylHiggsInput.charged_apply => Physics.WeylHiggsInput.charged_apply,
  GUT.WeylHiggsInput.charged_jets => Physics.WeylHiggsInput.charged_jets,
  GUT.WeylHiggsInput.combined_apply => Physics.WeylHiggsInput.combined_apply,
  GUT.WeylHiggsInput.derivative_covariant => Physics.WeylHiggsInput.derivative_covariant,
  GUT.WeylHiggsInput.directions => Physics.WeylHiggsInput.directions,
  GUT.WeylHiggsInput.equations => Physics.WeylHiggsInput.equations,
  GUT.WeylHiggsInput.fields => Physics.WeylHiggsInput.fields,
  GUT.WeylHiggsInput.grade_stable => Physics.WeylHiggsInput.grade_stable,
  GUT.WeylHiggsInput.inc_covariant => Physics.WeylHiggsInput.inc_covariant,
  GUT.WeylHiggsInput.input => Physics.WeylHiggsInput.input,
  GUT.WeylHiggsInput.instAddCommGroupA_physics => Physics.WeylHiggsInput.instAddCommGroupA_physics,
  GUT.WeylHiggsInput.instModuleComplexA_physics => Physics.WeylHiggsInput.instModuleComplexA_physics,
  GUT.WeylHiggsInput.instRingA_physics => Physics.WeylHiggsInput.instRingA_physics,
  GUT.WeylHiggsInput.jetInc_covariant => Physics.WeylHiggsInput.jetInc_covariant,
  GUT.WeylHiggsInput.jets => Physics.WeylHiggsInput.jets,
  GUT.WeylHiggsInput.oddInc_covariant => Physics.WeylHiggsInput.oddInc_covariant,
  GUT.WeylHiggsInput.scalarEmbed => Physics.WeylHiggsInput.scalarEmbed,
  GUT.WeylHiggsInput.scalar_equations => Physics.WeylHiggsInput.scalar_equations,
  GUT.WeylHiggsInput.seed_stable => Physics.WeylHiggsInput.seed_stable,
  GUT.WeylHiggsInput.selected => Physics.WeylHiggsInput.selected,
  GUT.WeylHiggsInput.stable => Physics.WeylHiggsInput.stable
]

assert_compatible GUT.WeylHiggsInput.Group => Physics.WeylHiggsInput.Group
assert_compatible GUT.WeylHiggsInput.V => Physics.WeylHiggsInput.V
assert_compatible GUT.WeylHiggsInput.action => Physics.WeylHiggsInput.action
assert_compatible GUT.WeylHiggsInput.bosons => Physics.WeylHiggsInput.bosons
assert_compatible GUT.WeylHiggsInput.charge => Physics.WeylHiggsInput.charge
assert_compatible GUT.WeylHiggsInput.charged => Physics.WeylHiggsInput.charged
assert_compatible GUT.WeylHiggsInput.charged_apply => Physics.WeylHiggsInput.charged_apply
assert_compatible GUT.WeylHiggsInput.charged_jets => Physics.WeylHiggsInput.charged_jets
assert_compatible GUT.WeylHiggsInput.combined_apply => Physics.WeylHiggsInput.combined_apply
assert_compatible GUT.WeylHiggsInput.derivative_covariant => Physics.WeylHiggsInput.derivative_covariant
assert_compatible GUT.WeylHiggsInput.directions => Physics.WeylHiggsInput.directions
assert_compatible GUT.WeylHiggsInput.equations => Physics.WeylHiggsInput.equations
assert_compatible GUT.WeylHiggsInput.fields => Physics.WeylHiggsInput.fields
assert_compatible GUT.WeylHiggsInput.grade_stable => Physics.WeylHiggsInput.grade_stable
assert_compatible GUT.WeylHiggsInput.inc_covariant => Physics.WeylHiggsInput.inc_covariant
assert_compatible GUT.WeylHiggsInput.input => Physics.WeylHiggsInput.input
assert_compatible GUT.WeylHiggsInput.instAddCommGroupA_physics => Physics.WeylHiggsInput.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsInput.instModuleComplexA_physics => Physics.WeylHiggsInput.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsInput.instRingA_physics => Physics.WeylHiggsInput.instRingA_physics
assert_compatible GUT.WeylHiggsInput.jetInc_covariant => Physics.WeylHiggsInput.jetInc_covariant
assert_compatible GUT.WeylHiggsInput.jets => Physics.WeylHiggsInput.jets
assert_compatible GUT.WeylHiggsInput.oddInc_covariant => Physics.WeylHiggsInput.oddInc_covariant
assert_compatible GUT.WeylHiggsInput.scalarEmbed => Physics.WeylHiggsInput.scalarEmbed
assert_compatible GUT.WeylHiggsInput.scalar_equations => Physics.WeylHiggsInput.scalar_equations
assert_compatible GUT.WeylHiggsInput.seed_stable => Physics.WeylHiggsInput.seed_stable
assert_compatible GUT.WeylHiggsInput.selected => Physics.WeylHiggsInput.selected
assert_compatible GUT.WeylHiggsInput.stable => Physics.WeylHiggsInput.stable
