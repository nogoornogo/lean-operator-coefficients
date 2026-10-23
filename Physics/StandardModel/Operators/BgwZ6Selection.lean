import Physics.StandardModel.Operators.Selection.BgwZ6Selection
import Physics.StandardModel.Operators.ComposableBLSupport
import Math.RepresentationTheory.CyclicCharge
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.BgwZ6Selection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BgwZ6Selection.all_forbidden => Physics.BgwZ6Selection.all_forbidden,
  GUT.BgwZ6Selection.baryon_divisible => Physics.BgwZ6Selection.baryon_divisible,
  GUT.BgwZ6Selection.boson_identity => Physics.BgwZ6Selection.boson_identity,
  GUT.BgwZ6Selection.bq => Physics.BgwZ6Selection.bq,
  GUT.BgwZ6Selection.bq.eq_1 => Physics.BgwZ6Selection.bq.eq_1,
  GUT.BgwZ6Selection.charge_of_nonzero => Physics.BgwZ6Selection.charge_of_nonzero,
  GUT.BgwZ6Selection.copies => Physics.BgwZ6Selection.copies,
  GUT.BgwZ6Selection.copies.eq_1 => Physics.BgwZ6Selection.copies.eq_1,
  GUT.BgwZ6Selection.fermion_conjugates => Physics.BgwZ6Selection.fermion_conjugates,
  GUT.BgwZ6Selection.fermion_identity => Physics.BgwZ6Selection.fermion_identity,
  GUT.BgwZ6Selection.field_scalar => Physics.BgwZ6Selection.field_scalar,
  GUT.BgwZ6Selection.flavor => Physics.BgwZ6Selection.flavor,
  GUT.BgwZ6Selection.flavor.eq_1 => Physics.BgwZ6Selection.flavor.eq_1,
  GUT.BgwZ6Selection.forbidden_values => Physics.BgwZ6Selection.forbidden_values,
  GUT.BgwZ6Selection.fq => Physics.BgwZ6Selection.fq,
  GUT.BgwZ6Selection.fq.eq_1 => Physics.BgwZ6Selection.fq.eq_1,
  GUT.BgwZ6Selection.higgs_conjugates => Physics.BgwZ6Selection.higgs_conjugates,
  GUT.BgwZ6Selection.llhh_neutral => Physics.BgwZ6Selection.llhh_neutral,
  GUT.BgwZ6Selection.printed_dictionary => Physics.BgwZ6Selection.printed_dictionary,
  GUT.BgwZ6Selection.residual_forbidden => Physics.BgwZ6Selection.residual_forbidden,
  GUT.BgwZ6Selection.scalarFlavor => Physics.BgwZ6Selection.scalarFlavor,
  GUT.BgwZ6Selection.scalarFlavor.eq_1 => Physics.BgwZ6Selection.scalarFlavor.eq_1,
  GUT.BgwZ6Selection.scalar_scalar => Physics.BgwZ6Selection.scalar_scalar,
  GUT.BgwZ6Selection.total => Physics.BgwZ6Selection.total,
  GUT.BgwZ6Selection.total.eq_1 => Physics.BgwZ6Selection.total.eq_1,
  GUT.BgwZ6Selection.total_identity => Physics.BgwZ6Selection.total_identity
]

assert_compatible GUT.BgwZ6Selection.all_forbidden => Physics.BgwZ6Selection.all_forbidden
assert_compatible GUT.BgwZ6Selection.baryon_divisible => Physics.BgwZ6Selection.baryon_divisible
assert_compatible GUT.BgwZ6Selection.boson_identity => Physics.BgwZ6Selection.boson_identity
assert_compatible GUT.BgwZ6Selection.bq => Physics.BgwZ6Selection.bq
assert_compatible GUT.BgwZ6Selection.bq.eq_1 => Physics.BgwZ6Selection.bq.eq_1
assert_compatible GUT.BgwZ6Selection.charge_of_nonzero => Physics.BgwZ6Selection.charge_of_nonzero
assert_compatible GUT.BgwZ6Selection.copies => Physics.BgwZ6Selection.copies
assert_compatible GUT.BgwZ6Selection.copies.eq_1 => Physics.BgwZ6Selection.copies.eq_1
assert_compatible GUT.BgwZ6Selection.fermion_conjugates => Physics.BgwZ6Selection.fermion_conjugates
assert_compatible GUT.BgwZ6Selection.fermion_identity => Physics.BgwZ6Selection.fermion_identity
assert_compatible GUT.BgwZ6Selection.field_scalar => Physics.BgwZ6Selection.field_scalar
assert_compatible GUT.BgwZ6Selection.flavor => Physics.BgwZ6Selection.flavor
assert_compatible GUT.BgwZ6Selection.flavor.eq_1 => Physics.BgwZ6Selection.flavor.eq_1
assert_compatible GUT.BgwZ6Selection.forbidden_values => Physics.BgwZ6Selection.forbidden_values
assert_compatible GUT.BgwZ6Selection.fq => Physics.BgwZ6Selection.fq
assert_compatible GUT.BgwZ6Selection.fq.eq_1 => Physics.BgwZ6Selection.fq.eq_1
assert_compatible GUT.BgwZ6Selection.higgs_conjugates => Physics.BgwZ6Selection.higgs_conjugates
assert_compatible GUT.BgwZ6Selection.llhh_neutral => Physics.BgwZ6Selection.llhh_neutral
assert_compatible GUT.BgwZ6Selection.printed_dictionary => Physics.BgwZ6Selection.printed_dictionary
assert_compatible GUT.BgwZ6Selection.residual_forbidden => Physics.BgwZ6Selection.residual_forbidden
assert_compatible GUT.BgwZ6Selection.scalarFlavor => Physics.BgwZ6Selection.scalarFlavor
assert_compatible GUT.BgwZ6Selection.scalarFlavor.eq_1 => Physics.BgwZ6Selection.scalarFlavor.eq_1
assert_compatible GUT.BgwZ6Selection.scalar_scalar => Physics.BgwZ6Selection.scalar_scalar
assert_compatible GUT.BgwZ6Selection.total => Physics.BgwZ6Selection.total
assert_compatible GUT.BgwZ6Selection.total.eq_1 => Physics.BgwZ6Selection.total.eq_1
assert_compatible GUT.BgwZ6Selection.total_identity => Physics.BgwZ6Selection.total_identity
