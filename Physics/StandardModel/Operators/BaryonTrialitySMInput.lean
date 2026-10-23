import Physics.StandardModel.Operators.Selection.BaryonTrialitySMInput
import Physics.StandardModel.Operators.ComposableBLSupport
import Math.RepresentationTheory.CyclicCharge
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.BaryonTrialitySMInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BaryonTrialitySMInput.all_forbidden => Physics.BaryonTrialitySMInput.all_forbidden,
  GUT.BaryonTrialitySMInput.baryon_divisible => Physics.BaryonTrialitySMInput.baryon_divisible,
  GUT.BaryonTrialitySMInput.boson_identity => Physics.BaryonTrialitySMInput.boson_identity,
  GUT.BaryonTrialitySMInput.bq => Physics.BaryonTrialitySMInput.bq,
  GUT.BaryonTrialitySMInput.bq.eq_1 => Physics.BaryonTrialitySMInput.bq.eq_1,
  GUT.BaryonTrialitySMInput.charge_of_nonzero => Physics.BaryonTrialitySMInput.charge_of_nonzero,
  GUT.BaryonTrialitySMInput.component_dictionary => Physics.BaryonTrialitySMInput.component_dictionary,
  GUT.BaryonTrialitySMInput.copies => Physics.BaryonTrialitySMInput.copies,
  GUT.BaryonTrialitySMInput.copies.eq_1 => Physics.BaryonTrialitySMInput.copies.eq_1,
  GUT.BaryonTrialitySMInput.fermion_identity => Physics.BaryonTrialitySMInput.fermion_identity,
  GUT.BaryonTrialitySMInput.field_scalar => Physics.BaryonTrialitySMInput.field_scalar,
  GUT.BaryonTrialitySMInput.flavor => Physics.BaryonTrialitySMInput.flavor,
  GUT.BaryonTrialitySMInput.flavor.eq_1 => Physics.BaryonTrialitySMInput.flavor.eq_1,
  GUT.BaryonTrialitySMInput.forbidden_values => Physics.BaryonTrialitySMInput.forbidden_values,
  GUT.BaryonTrialitySMInput.fq => Physics.BaryonTrialitySMInput.fq,
  GUT.BaryonTrialitySMInput.fq.eq_1 => Physics.BaryonTrialitySMInput.fq.eq_1,
  GUT.BaryonTrialitySMInput.residual_forbidden => Physics.BaryonTrialitySMInput.residual_forbidden,
  GUT.BaryonTrialitySMInput.scalarFlavor => Physics.BaryonTrialitySMInput.scalarFlavor,
  GUT.BaryonTrialitySMInput.scalarFlavor.eq_1 => Physics.BaryonTrialitySMInput.scalarFlavor.eq_1,
  GUT.BaryonTrialitySMInput.scalar_scalar => Physics.BaryonTrialitySMInput.scalar_scalar,
  GUT.BaryonTrialitySMInput.total => Physics.BaryonTrialitySMInput.total,
  GUT.BaryonTrialitySMInput.total.eq_1 => Physics.BaryonTrialitySMInput.total.eq_1,
  GUT.BaryonTrialitySMInput.total_identity => Physics.BaryonTrialitySMInput.total_identity
]

assert_compatible GUT.BaryonTrialitySMInput.all_forbidden => Physics.BaryonTrialitySMInput.all_forbidden
assert_compatible GUT.BaryonTrialitySMInput.baryon_divisible => Physics.BaryonTrialitySMInput.baryon_divisible
assert_compatible GUT.BaryonTrialitySMInput.boson_identity => Physics.BaryonTrialitySMInput.boson_identity
assert_compatible GUT.BaryonTrialitySMInput.bq => Physics.BaryonTrialitySMInput.bq
assert_compatible GUT.BaryonTrialitySMInput.bq.eq_1 => Physics.BaryonTrialitySMInput.bq.eq_1
assert_compatible GUT.BaryonTrialitySMInput.charge_of_nonzero => Physics.BaryonTrialitySMInput.charge_of_nonzero
assert_compatible GUT.BaryonTrialitySMInput.component_dictionary => Physics.BaryonTrialitySMInput.component_dictionary
assert_compatible GUT.BaryonTrialitySMInput.copies => Physics.BaryonTrialitySMInput.copies
assert_compatible GUT.BaryonTrialitySMInput.copies.eq_1 => Physics.BaryonTrialitySMInput.copies.eq_1
assert_compatible GUT.BaryonTrialitySMInput.fermion_identity => Physics.BaryonTrialitySMInput.fermion_identity
assert_compatible GUT.BaryonTrialitySMInput.field_scalar => Physics.BaryonTrialitySMInput.field_scalar
assert_compatible GUT.BaryonTrialitySMInput.flavor => Physics.BaryonTrialitySMInput.flavor
assert_compatible GUT.BaryonTrialitySMInput.flavor.eq_1 => Physics.BaryonTrialitySMInput.flavor.eq_1
assert_compatible GUT.BaryonTrialitySMInput.forbidden_values => Physics.BaryonTrialitySMInput.forbidden_values
assert_compatible GUT.BaryonTrialitySMInput.fq => Physics.BaryonTrialitySMInput.fq
assert_compatible GUT.BaryonTrialitySMInput.fq.eq_1 => Physics.BaryonTrialitySMInput.fq.eq_1
assert_compatible GUT.BaryonTrialitySMInput.residual_forbidden => Physics.BaryonTrialitySMInput.residual_forbidden
assert_compatible GUT.BaryonTrialitySMInput.scalarFlavor => Physics.BaryonTrialitySMInput.scalarFlavor
assert_compatible GUT.BaryonTrialitySMInput.scalarFlavor.eq_1 => Physics.BaryonTrialitySMInput.scalarFlavor.eq_1
assert_compatible GUT.BaryonTrialitySMInput.scalar_scalar => Physics.BaryonTrialitySMInput.scalar_scalar
assert_compatible GUT.BaryonTrialitySMInput.total => Physics.BaryonTrialitySMInput.total
assert_compatible GUT.BaryonTrialitySMInput.total.eq_1 => Physics.BaryonTrialitySMInput.total.eq_1
assert_compatible GUT.BaryonTrialitySMInput.total_identity => Physics.BaryonTrialitySMInput.total_identity
