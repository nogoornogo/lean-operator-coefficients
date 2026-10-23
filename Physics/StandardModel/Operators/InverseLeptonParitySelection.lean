import Physics.StandardModel.Operators.Selection.InverseLeptonParitySelection
import Physics.StandardModel.Operators.ComposableBLSupport
import Math.RepresentationTheory.CyclicCharge
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.InverseLeptonParitySelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InverseLeptonParitySelection.all_forbidden => Physics.InverseLeptonParitySelection.all_forbidden,
  GUT.InverseLeptonParitySelection.baryon_even => Physics.InverseLeptonParitySelection.baryon_even,
  GUT.InverseLeptonParitySelection.bq => Physics.InverseLeptonParitySelection.bq,
  GUT.InverseLeptonParitySelection.bq.eq_1 => Physics.InverseLeptonParitySelection.bq.eq_1,
  GUT.InverseLeptonParitySelection.charge_of_nonzero => Physics.InverseLeptonParitySelection.charge_of_nonzero,
  GUT.InverseLeptonParitySelection.content_parity => Physics.InverseLeptonParitySelection.content_parity,
  GUT.InverseLeptonParitySelection.copies => Physics.InverseLeptonParitySelection.copies,
  GUT.InverseLeptonParitySelection.copies.eq_1 => Physics.InverseLeptonParitySelection.copies.eq_1,
  GUT.InverseLeptonParitySelection.field_scalar => Physics.InverseLeptonParitySelection.field_scalar,
  GUT.InverseLeptonParitySelection.flavor => Physics.InverseLeptonParitySelection.flavor,
  GUT.InverseLeptonParitySelection.flavor.eq_1 => Physics.InverseLeptonParitySelection.flavor.eq_1,
  GUT.InverseLeptonParitySelection.forbidden_values => Physics.InverseLeptonParitySelection.forbidden_values,
  GUT.InverseLeptonParitySelection.fq => Physics.InverseLeptonParitySelection.fq,
  GUT.InverseLeptonParitySelection.fq.eq_1 => Physics.InverseLeptonParitySelection.fq.eq_1,
  GUT.InverseLeptonParitySelection.residual_forbidden => Physics.InverseLeptonParitySelection.residual_forbidden,
  GUT.InverseLeptonParitySelection.scalarFlavor => Physics.InverseLeptonParitySelection.scalarFlavor,
  GUT.InverseLeptonParitySelection.scalarFlavor.eq_1 => Physics.InverseLeptonParitySelection.scalarFlavor.eq_1,
  GUT.InverseLeptonParitySelection.scalar_scalar => Physics.InverseLeptonParitySelection.scalar_scalar,
  GUT.InverseLeptonParitySelection.species_parity => Physics.InverseLeptonParitySelection.species_parity,
  GUT.InverseLeptonParitySelection.target => Physics.InverseLeptonParitySelection.target,
  GUT.InverseLeptonParitySelection.total => Physics.InverseLeptonParitySelection.total,
  GUT.InverseLeptonParitySelection.total.eq_1 => Physics.InverseLeptonParitySelection.total.eq_1,
  GUT.InverseLeptonParitySelection.total_lepton => Physics.InverseLeptonParitySelection.total_lepton
]

assert_compatible GUT.InverseLeptonParitySelection.all_forbidden => Physics.InverseLeptonParitySelection.all_forbidden
assert_compatible GUT.InverseLeptonParitySelection.baryon_even => Physics.InverseLeptonParitySelection.baryon_even
assert_compatible GUT.InverseLeptonParitySelection.bq => Physics.InverseLeptonParitySelection.bq
assert_compatible GUT.InverseLeptonParitySelection.bq.eq_1 => Physics.InverseLeptonParitySelection.bq.eq_1
assert_compatible GUT.InverseLeptonParitySelection.charge_of_nonzero => Physics.InverseLeptonParitySelection.charge_of_nonzero
assert_compatible GUT.InverseLeptonParitySelection.content_parity => Physics.InverseLeptonParitySelection.content_parity
assert_compatible GUT.InverseLeptonParitySelection.copies => Physics.InverseLeptonParitySelection.copies
assert_compatible GUT.InverseLeptonParitySelection.copies.eq_1 => Physics.InverseLeptonParitySelection.copies.eq_1
assert_compatible GUT.InverseLeptonParitySelection.field_scalar => Physics.InverseLeptonParitySelection.field_scalar
assert_compatible GUT.InverseLeptonParitySelection.flavor => Physics.InverseLeptonParitySelection.flavor
assert_compatible GUT.InverseLeptonParitySelection.flavor.eq_1 => Physics.InverseLeptonParitySelection.flavor.eq_1
assert_compatible GUT.InverseLeptonParitySelection.forbidden_values => Physics.InverseLeptonParitySelection.forbidden_values
assert_compatible GUT.InverseLeptonParitySelection.fq => Physics.InverseLeptonParitySelection.fq
assert_compatible GUT.InverseLeptonParitySelection.fq.eq_1 => Physics.InverseLeptonParitySelection.fq.eq_1
assert_compatible GUT.InverseLeptonParitySelection.residual_forbidden => Physics.InverseLeptonParitySelection.residual_forbidden
assert_compatible GUT.InverseLeptonParitySelection.scalarFlavor => Physics.InverseLeptonParitySelection.scalarFlavor
assert_compatible GUT.InverseLeptonParitySelection.scalarFlavor.eq_1 => Physics.InverseLeptonParitySelection.scalarFlavor.eq_1
assert_compatible GUT.InverseLeptonParitySelection.scalar_scalar => Physics.InverseLeptonParitySelection.scalar_scalar
assert_compatible GUT.InverseLeptonParitySelection.species_parity => Physics.InverseLeptonParitySelection.species_parity
assert_compatible GUT.InverseLeptonParitySelection.target => Physics.InverseLeptonParitySelection.target
assert_compatible GUT.InverseLeptonParitySelection.total => Physics.InverseLeptonParitySelection.total
assert_compatible GUT.InverseLeptonParitySelection.total.eq_1 => Physics.InverseLeptonParitySelection.total.eq_1
assert_compatible GUT.InverseLeptonParitySelection.total_lepton => Physics.InverseLeptonParitySelection.total_lepton
