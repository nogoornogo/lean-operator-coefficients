import Physics.FieldTheory.Jets.Lagrangian.InteractingLagrangianLiterature
import Math.RepresentationTheory.BosonicAllOrderCoordinates
import Physics.FieldTheory.Jets.DerivativeLiteratureRecheck
import Physics.FieldTheory.Jets.ScalarConstantCoefficients
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lagrangian.InteractingLagrangianLiterature instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InteractingLagrangianLiterature.Higgs.complete_roundtrip => Physics.InteractingLagrangianLiterature.Higgs.complete_roundtrip,
  GUT.InteractingLagrangianLiterature.Higgs.equivalence => Physics.InteractingLagrangianLiterature.Higgs.equivalence,
  GUT.InteractingLagrangianLiterature.Higgs.paper_relation => Physics.InteractingLagrangianLiterature.Higgs.paper_relation,
  GUT.InteractingLagrangianLiterature.Higgs.presentation => Physics.InteractingLagrangianLiterature.Higgs.presentation,
  GUT.InteractingLagrangianLiterature.Scalar.cubic_value_iff => Physics.InteractingLagrangianLiterature.Scalar.cubic_value_iff,
  GUT.InteractingLagrangianLiterature.Scalar.equivalence => Physics.InteractingLagrangianLiterature.Scalar.equivalence,
  GUT.InteractingLagrangianLiterature.Scalar.first_order_on_shell => Physics.InteractingLagrangianLiterature.Scalar.first_order_on_shell,
  GUT.InteractingLagrangianLiterature.Scalar.higher_order_not_erased => Physics.InteractingLagrangianLiterature.Scalar.higher_order_not_erased,
  GUT.InteractingLagrangianLiterature.Scalar.presentation => Physics.InteractingLagrangianLiterature.Scalar.presentation,
  GUT.InteractingLagrangianLiterature.TongYukawa.A => Physics.InteractingLagrangianLiterature.TongYukawa.A,
  GUT.InteractingLagrangianLiterature.TongYukawa.E => Physics.InteractingLagrangianLiterature.TongYukawa.E,
  GUT.InteractingLagrangianLiterature.TongYukawa.Label => Physics.InteractingLagrangianLiterature.TongYukawa.Label,
  GUT.InteractingLagrangianLiterature.TongYukawa.barred_euler => Physics.InteractingLagrangianLiterature.TongYukawa.barred_euler,
  GUT.InteractingLagrangianLiterature.TongYukawa.bilinear => Physics.InteractingLagrangianLiterature.TongYukawa.bilinear,
  GUT.InteractingLagrangianLiterature.TongYukawa.bilinear.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.bilinear.eq_1,
  GUT.InteractingLagrangianLiterature.TongYukawa.complete_roundtrip => Physics.InteractingLagrangianLiterature.TongYukawa.complete_roundtrip,
  GUT.InteractingLagrangianLiterature.TongYukawa.density => Physics.InteractingLagrangianLiterature.TongYukawa.density,
  GUT.InteractingLagrangianLiterature.TongYukawa.density.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.density.eq_1,
  GUT.InteractingLagrangianLiterature.TongYukawa.density_eval => Physics.InteractingLagrangianLiterature.TongYukawa.density_eval,
  GUT.InteractingLagrangianLiterature.TongYukawa.equivalence => Physics.InteractingLagrangianLiterature.TongYukawa.equivalence,
  GUT.InteractingLagrangianLiterature.TongYukawa.input => Physics.InteractingLagrangianLiterature.TongYukawa.input,
  GUT.InteractingLagrangianLiterature.TongYukawa.instAddCommGroupA => Physics.InteractingLagrangianLiterature.TongYukawa.instAddCommGroupA,
  GUT.InteractingLagrangianLiterature.TongYukawa.instModuleComplexA => Physics.InteractingLagrangianLiterature.TongYukawa.instModuleComplexA,
  GUT.InteractingLagrangianLiterature.TongYukawa.instRingA => Physics.InteractingLagrangianLiterature.TongYukawa.instRingA,
  GUT.InteractingLagrangianLiterature.TongYukawa.pair => Physics.InteractingLagrangianLiterature.TongYukawa.pair,
  GUT.InteractingLagrangianLiterature.TongYukawa.pair.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.pair.eq_1,
  GUT.InteractingLagrangianLiterature.TongYukawa.phi => Physics.InteractingLagrangianLiterature.TongYukawa.phi,
  GUT.InteractingLagrangianLiterature.TongYukawa.phi.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.phi.eq_1,
  GUT.InteractingLagrangianLiterature.TongYukawa.presentation => Physics.InteractingLagrangianLiterature.TongYukawa.presentation,
  GUT.InteractingLagrangianLiterature.TongYukawa.scalar_euler => Physics.InteractingLagrangianLiterature.TongYukawa.scalar_euler,
  GUT.InteractingLagrangianLiterature.TongYukawa.spinor => Physics.InteractingLagrangianLiterature.TongYukawa.spinor,
  GUT.InteractingLagrangianLiterature.TongYukawa.spinor.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.spinor.eq_1,
  GUT.InteractingLagrangianLiterature.TongYukawa.unbarred_euler => Physics.InteractingLagrangianLiterature.TongYukawa.unbarred_euler
]

assert_compatible GUT.InteractingLagrangianLiterature.Higgs.complete_roundtrip => Physics.InteractingLagrangianLiterature.Higgs.complete_roundtrip
assert_compatible GUT.InteractingLagrangianLiterature.Higgs.equivalence => Physics.InteractingLagrangianLiterature.Higgs.equivalence
assert_compatible GUT.InteractingLagrangianLiterature.Higgs.paper_relation => Physics.InteractingLagrangianLiterature.Higgs.paper_relation
assert_compatible GUT.InteractingLagrangianLiterature.Higgs.presentation => Physics.InteractingLagrangianLiterature.Higgs.presentation
assert_compatible GUT.InteractingLagrangianLiterature.Scalar.cubic_value_iff => Physics.InteractingLagrangianLiterature.Scalar.cubic_value_iff
assert_compatible GUT.InteractingLagrangianLiterature.Scalar.equivalence => Physics.InteractingLagrangianLiterature.Scalar.equivalence
assert_compatible GUT.InteractingLagrangianLiterature.Scalar.first_order_on_shell => Physics.InteractingLagrangianLiterature.Scalar.first_order_on_shell
assert_compatible GUT.InteractingLagrangianLiterature.Scalar.higher_order_not_erased => Physics.InteractingLagrangianLiterature.Scalar.higher_order_not_erased
assert_compatible GUT.InteractingLagrangianLiterature.Scalar.presentation => Physics.InteractingLagrangianLiterature.Scalar.presentation
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.A => Physics.InteractingLagrangianLiterature.TongYukawa.A
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.E => Physics.InteractingLagrangianLiterature.TongYukawa.E
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.Label => Physics.InteractingLagrangianLiterature.TongYukawa.Label
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.barred_euler => Physics.InteractingLagrangianLiterature.TongYukawa.barred_euler
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.bilinear => Physics.InteractingLagrangianLiterature.TongYukawa.bilinear
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.bilinear.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.bilinear.eq_1
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.complete_roundtrip => Physics.InteractingLagrangianLiterature.TongYukawa.complete_roundtrip
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.density => Physics.InteractingLagrangianLiterature.TongYukawa.density
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.density.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.density.eq_1
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.density_eval => Physics.InteractingLagrangianLiterature.TongYukawa.density_eval
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.equivalence => Physics.InteractingLagrangianLiterature.TongYukawa.equivalence
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.input => Physics.InteractingLagrangianLiterature.TongYukawa.input
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.instAddCommGroupA => Physics.InteractingLagrangianLiterature.TongYukawa.instAddCommGroupA
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.instModuleComplexA => Physics.InteractingLagrangianLiterature.TongYukawa.instModuleComplexA
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.instRingA => Physics.InteractingLagrangianLiterature.TongYukawa.instRingA
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.pair => Physics.InteractingLagrangianLiterature.TongYukawa.pair
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.pair.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.pair.eq_1
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.phi => Physics.InteractingLagrangianLiterature.TongYukawa.phi
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.phi.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.phi.eq_1
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.presentation => Physics.InteractingLagrangianLiterature.TongYukawa.presentation
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.scalar_euler => Physics.InteractingLagrangianLiterature.TongYukawa.scalar_euler
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.spinor => Physics.InteractingLagrangianLiterature.TongYukawa.spinor
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.spinor.eq_1 => Physics.InteractingLagrangianLiterature.TongYukawa.spinor.eq_1
assert_compatible GUT.InteractingLagrangianLiterature.TongYukawa.unbarred_euler => Physics.InteractingLagrangianLiterature.TongYukawa.unbarred_euler
