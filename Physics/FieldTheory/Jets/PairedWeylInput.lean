import Physics.FieldTheory.Jets.Weyl.Equations.PairedWeylInput
import Math.Algebra.PairedWeylKinetic
import Math.RepresentationTheory.PairedComponentFields
import Math.RepresentationTheory.TwoSidedCovariance
import Physics.FieldTheory.Jets.ConjugateWeylEquation
import Physics.FieldTheory.Jets.DerivativeLiteratureMixed
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.PairedWeylInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PairedWeylInput.Group => Physics.PairedWeylInput.Group,
  GUT.PairedWeylInput.action => Physics.PairedWeylInput.action,
  GUT.PairedWeylInput.bosons => Physics.PairedWeylInput.bosons,
  GUT.PairedWeylInput.derivative_covariant => Physics.PairedWeylInput.derivative_covariant,
  GUT.PairedWeylInput.direct => Physics.PairedWeylInput.direct,
  GUT.PairedWeylInput.equations => Physics.PairedWeylInput.equations,
  GUT.PairedWeylInput.fieldSplit => Physics.PairedWeylInput.fieldSplit,
  GUT.PairedWeylInput.fieldSplit.eq_1 => Physics.PairedWeylInput.fieldSplit.eq_1,
  GUT.PairedWeylInput.fields => Physics.PairedWeylInput.fields,
  GUT.PairedWeylInput.inc => Physics.PairedWeylInput.inc,
  GUT.PairedWeylInput.inc.eq_1 => Physics.PairedWeylInput.inc.eq_1,
  GUT.PairedWeylInput.inc_covariant => Physics.PairedWeylInput.inc_covariant,
  GUT.PairedWeylInput.inc_single => Physics.PairedWeylInput.inc_single,
  GUT.PairedWeylInput.instAddCommGroupA_physics => Physics.PairedWeylInput.instAddCommGroupA_physics,
  GUT.PairedWeylInput.instModuleComplexA_physics => Physics.PairedWeylInput.instModuleComplexA_physics,
  GUT.PairedWeylInput.instRingA_physics => Physics.PairedWeylInput.instRingA_physics,
  GUT.PairedWeylInput.jetInc => Physics.PairedWeylInput.jetInc,
  GUT.PairedWeylInput.jetInc.eq_1 => Physics.PairedWeylInput.jetInc.eq_1,
  GUT.PairedWeylInput.jetInc_covariant => Physics.PairedWeylInput.jetInc_covariant,
  GUT.PairedWeylInput.jetInc_single => Physics.PairedWeylInput.jetInc_single,
  GUT.PairedWeylInput.jets => Physics.PairedWeylInput.jets,
  GUT.PairedWeylInput.leftSeed => Physics.PairedWeylInput.leftSeed,
  GUT.PairedWeylInput.left_covariant => Physics.PairedWeylInput.left_covariant,
  GUT.PairedWeylInput.oddInc => Physics.PairedWeylInput.oddInc,
  GUT.PairedWeylInput.oddInc_covariant => Physics.PairedWeylInput.oddInc_covariant,
  GUT.PairedWeylInput.oddVector_covariant => Physics.PairedWeylInput.oddVector_covariant,
  GUT.PairedWeylInput.rightSeed => Physics.PairedWeylInput.rightSeed,
  GUT.PairedWeylInput.right_covariant => Physics.PairedWeylInput.right_covariant,
  GUT.PairedWeylInput.stable => Physics.PairedWeylInput.stable
]

assert_compatible GUT.PairedWeylInput.Group => Physics.PairedWeylInput.Group
assert_compatible GUT.PairedWeylInput.action => Physics.PairedWeylInput.action
assert_compatible GUT.PairedWeylInput.bosons => Physics.PairedWeylInput.bosons
assert_compatible GUT.PairedWeylInput.derivative_covariant => Physics.PairedWeylInput.derivative_covariant
assert_compatible GUT.PairedWeylInput.direct => Physics.PairedWeylInput.direct
assert_compatible GUT.PairedWeylInput.equations => Physics.PairedWeylInput.equations
assert_compatible GUT.PairedWeylInput.fieldSplit => Physics.PairedWeylInput.fieldSplit
assert_compatible GUT.PairedWeylInput.fieldSplit.eq_1 => Physics.PairedWeylInput.fieldSplit.eq_1
assert_compatible GUT.PairedWeylInput.fields => Physics.PairedWeylInput.fields
assert_compatible GUT.PairedWeylInput.inc => Physics.PairedWeylInput.inc
assert_compatible GUT.PairedWeylInput.inc.eq_1 => Physics.PairedWeylInput.inc.eq_1
assert_compatible GUT.PairedWeylInput.inc_covariant => Physics.PairedWeylInput.inc_covariant
assert_compatible GUT.PairedWeylInput.inc_single => Physics.PairedWeylInput.inc_single
assert_compatible GUT.PairedWeylInput.instAddCommGroupA_physics => Physics.PairedWeylInput.instAddCommGroupA_physics
assert_compatible GUT.PairedWeylInput.instModuleComplexA_physics => Physics.PairedWeylInput.instModuleComplexA_physics
assert_compatible GUT.PairedWeylInput.instRingA_physics => Physics.PairedWeylInput.instRingA_physics
assert_compatible GUT.PairedWeylInput.jetInc => Physics.PairedWeylInput.jetInc
assert_compatible GUT.PairedWeylInput.jetInc.eq_1 => Physics.PairedWeylInput.jetInc.eq_1
assert_compatible GUT.PairedWeylInput.jetInc_covariant => Physics.PairedWeylInput.jetInc_covariant
assert_compatible GUT.PairedWeylInput.jetInc_single => Physics.PairedWeylInput.jetInc_single
assert_compatible GUT.PairedWeylInput.jets => Physics.PairedWeylInput.jets
assert_compatible GUT.PairedWeylInput.leftSeed => Physics.PairedWeylInput.leftSeed
assert_compatible GUT.PairedWeylInput.left_covariant => Physics.PairedWeylInput.left_covariant
assert_compatible GUT.PairedWeylInput.oddInc => Physics.PairedWeylInput.oddInc
assert_compatible GUT.PairedWeylInput.oddInc_covariant => Physics.PairedWeylInput.oddInc_covariant
assert_compatible GUT.PairedWeylInput.oddVector_covariant => Physics.PairedWeylInput.oddVector_covariant
assert_compatible GUT.PairedWeylInput.rightSeed => Physics.PairedWeylInput.rightSeed
assert_compatible GUT.PairedWeylInput.right_covariant => Physics.PairedWeylInput.right_covariant
assert_compatible GUT.PairedWeylInput.stable => Physics.PairedWeylInput.stable
