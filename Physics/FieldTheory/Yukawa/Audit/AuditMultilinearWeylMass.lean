import Physics.FieldTheory.Yukawa.Mass.Audit.AuditMultilinearWeylMass
import Physics.FieldTheory.Yukawa.MultilinearWeylMassContinuity
import Physics.FieldTheory.Yukawa.WeylMassPolynomial
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.Audit.AuditMultilinearWeylMass instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AuditMultilinearWeylMass.chargedCoefficient => Physics.AuditMultilinearWeylMass.chargedCoefficient,
  GUT.AuditMultilinearWeylMass.chargedFamily => Physics.AuditMultilinearWeylMass.chargedFamily,
  GUT.AuditMultilinearWeylMass.chargedMass => Physics.AuditMultilinearWeylMass.chargedMass,
  GUT.AuditMultilinearWeylMass.chargedMass_invariant => Physics.AuditMultilinearWeylMass.chargedMass_invariant,
  GUT.AuditMultilinearWeylMass.chargedMass_nonzero => Physics.AuditMultilinearWeylMass.chargedMass_nonzero,
  GUT.AuditMultilinearWeylMass.charged_zero_mass => Physics.AuditMultilinearWeylMass.charged_zero_mass,
  GUT.AuditMultilinearWeylMass.conjugateFamily => Physics.AuditMultilinearWeylMass.conjugateFamily,
  GUT.AuditMultilinearWeylMass.conjugateFamily_apply => Physics.AuditMultilinearWeylMass.conjugateFamily_apply,
  GUT.AuditMultilinearWeylMass.conjugateFamily_continuous => Physics.AuditMultilinearWeylMass.conjugateFamily_continuous,
  GUT.AuditMultilinearWeylMass.conjugateFamily_not_complex_quadratic => Physics.AuditMultilinearWeylMass.conjugateFamily_not_complex_quadratic,
  GUT.AuditMultilinearWeylMass.conjugateFamily_zero => Physics.AuditMultilinearWeylMass.conjugateFamily_zero,
  GUT.AuditMultilinearWeylMass.conjugateSlot_not_complex_linear => Physics.AuditMultilinearWeylMass.conjugateSlot_not_complex_linear,
  GUT.AuditMultilinearWeylMass.conjugateSlots => Physics.AuditMultilinearWeylMass.conjugateSlots,
  GUT.AuditMultilinearWeylMass.conjugateSlots.eq_1 => Physics.AuditMultilinearWeylMass.conjugateSlots.eq_1,
  GUT.AuditMultilinearWeylMass.degree_zero_survives => Physics.AuditMultilinearWeylMass.degree_zero_survives,
  GUT.AuditMultilinearWeylMass.mixedFamily => Physics.AuditMultilinearWeylMass.mixedFamily,
  GUT.AuditMultilinearWeylMass.mixedFamily_apply => Physics.AuditMultilinearWeylMass.mixedFamily_apply,
  GUT.AuditMultilinearWeylMass.mixedFamily_continuous => Physics.AuditMultilinearWeylMass.mixedFamily_continuous,
  GUT.AuditMultilinearWeylMass.mixedSlots => Physics.AuditMultilinearWeylMass.mixedSlots,
  GUT.AuditMultilinearWeylMass.mixedSlots.eq_1 => Physics.AuditMultilinearWeylMass.mixedSlots.eq_1,
  GUT.AuditMultilinearWeylMass.mixed_two_fields_required => Physics.AuditMultilinearWeylMass.mixed_two_fields_required,
  GUT.AuditMultilinearWeylMass.polynomialFamily => Physics.AuditMultilinearWeylMass.polynomialFamily,
  GUT.AuditMultilinearWeylMass.polynomialFamily.eq_1 => Physics.AuditMultilinearWeylMass.polynomialFamily.eq_1,
  GUT.AuditMultilinearWeylMass.polynomialFamily_apply => Physics.AuditMultilinearWeylMass.polynomialFamily_apply,
  GUT.AuditMultilinearWeylMass.polynomialFamily_continuous => Physics.AuditMultilinearWeylMass.polynomialFamily_continuous,
  GUT.AuditMultilinearWeylMass.positive_degree_sum_zero => Physics.AuditMultilinearWeylMass.positive_degree_sum_zero,
  GUT.AuditMultilinearWeylMass.powerFamily => Physics.AuditMultilinearWeylMass.powerFamily,
  GUT.AuditMultilinearWeylMass.powerFamily_apply => Physics.AuditMultilinearWeylMass.powerFamily_apply,
  GUT.AuditMultilinearWeylMass.powerFamily_continuous => Physics.AuditMultilinearWeylMass.powerFamily_continuous,
  GUT.AuditMultilinearWeylMass.powerFamily_zero => Physics.AuditMultilinearWeylMass.powerFamily_zero,
  GUT.AuditMultilinearWeylMass.productCoupling => Physics.AuditMultilinearWeylMass.productCoupling,
  GUT.AuditMultilinearWeylMass.quadraticMass => Physics.AuditMultilinearWeylMass.quadraticMass,
  GUT.AuditMultilinearWeylMass.quadraticMass.eq_1 => Physics.AuditMultilinearWeylMass.quadraticMass.eq_1,
  GUT.AuditMultilinearWeylMass.quadraticMass_nonzero => Physics.AuditMultilinearWeylMass.quadraticMass_nonzero,
  GUT.AuditMultilinearWeylMass.quadratic_not_additive => Physics.AuditMultilinearWeylMass.quadratic_not_additive,
  GUT.AuditMultilinearWeylMass.trivial => Physics.AuditMultilinearWeylMass.trivial,
  GUT.AuditMultilinearWeylMass.trivialPair => Physics.AuditMultilinearWeylMass.trivialPair,
  GUT.AuditMultilinearWeylMass.weight => Physics.AuditMultilinearWeylMass.weight,
  GUT.WeylMassFamily.EquivariantFamily.atVacuum.eq_1 => Physics.WeylMassFamily.EquivariantFamily.atVacuum.eq_1
]

assert_compatible GUT.AuditMultilinearWeylMass.chargedCoefficient => Physics.AuditMultilinearWeylMass.chargedCoefficient
assert_compatible GUT.AuditMultilinearWeylMass.chargedFamily => Physics.AuditMultilinearWeylMass.chargedFamily
assert_compatible GUT.AuditMultilinearWeylMass.chargedMass => Physics.AuditMultilinearWeylMass.chargedMass
assert_compatible GUT.AuditMultilinearWeylMass.chargedMass_invariant => Physics.AuditMultilinearWeylMass.chargedMass_invariant
assert_compatible GUT.AuditMultilinearWeylMass.chargedMass_nonzero => Physics.AuditMultilinearWeylMass.chargedMass_nonzero
assert_compatible GUT.AuditMultilinearWeylMass.charged_zero_mass => Physics.AuditMultilinearWeylMass.charged_zero_mass
assert_compatible GUT.AuditMultilinearWeylMass.conjugateFamily => Physics.AuditMultilinearWeylMass.conjugateFamily
assert_compatible GUT.AuditMultilinearWeylMass.conjugateFamily_apply => Physics.AuditMultilinearWeylMass.conjugateFamily_apply
assert_compatible GUT.AuditMultilinearWeylMass.conjugateFamily_continuous => Physics.AuditMultilinearWeylMass.conjugateFamily_continuous
assert_compatible GUT.AuditMultilinearWeylMass.conjugateFamily_not_complex_quadratic => Physics.AuditMultilinearWeylMass.conjugateFamily_not_complex_quadratic
assert_compatible GUT.AuditMultilinearWeylMass.conjugateFamily_zero => Physics.AuditMultilinearWeylMass.conjugateFamily_zero
assert_compatible GUT.AuditMultilinearWeylMass.conjugateSlot_not_complex_linear => Physics.AuditMultilinearWeylMass.conjugateSlot_not_complex_linear
assert_compatible GUT.AuditMultilinearWeylMass.conjugateSlots => Physics.AuditMultilinearWeylMass.conjugateSlots
assert_compatible GUT.AuditMultilinearWeylMass.conjugateSlots.eq_1 => Physics.AuditMultilinearWeylMass.conjugateSlots.eq_1
assert_compatible GUT.AuditMultilinearWeylMass.degree_zero_survives => Physics.AuditMultilinearWeylMass.degree_zero_survives
assert_compatible GUT.AuditMultilinearWeylMass.mixedFamily => Physics.AuditMultilinearWeylMass.mixedFamily
assert_compatible GUT.AuditMultilinearWeylMass.mixedFamily_apply => Physics.AuditMultilinearWeylMass.mixedFamily_apply
assert_compatible GUT.AuditMultilinearWeylMass.mixedFamily_continuous => Physics.AuditMultilinearWeylMass.mixedFamily_continuous
assert_compatible GUT.AuditMultilinearWeylMass.mixedSlots => Physics.AuditMultilinearWeylMass.mixedSlots
assert_compatible GUT.AuditMultilinearWeylMass.mixedSlots.eq_1 => Physics.AuditMultilinearWeylMass.mixedSlots.eq_1
assert_compatible GUT.AuditMultilinearWeylMass.mixed_two_fields_required => Physics.AuditMultilinearWeylMass.mixed_two_fields_required
assert_compatible GUT.AuditMultilinearWeylMass.polynomialFamily => Physics.AuditMultilinearWeylMass.polynomialFamily
assert_compatible GUT.AuditMultilinearWeylMass.polynomialFamily.eq_1 => Physics.AuditMultilinearWeylMass.polynomialFamily.eq_1
assert_compatible GUT.AuditMultilinearWeylMass.polynomialFamily_apply => Physics.AuditMultilinearWeylMass.polynomialFamily_apply
assert_compatible GUT.AuditMultilinearWeylMass.polynomialFamily_continuous => Physics.AuditMultilinearWeylMass.polynomialFamily_continuous
assert_compatible GUT.AuditMultilinearWeylMass.positive_degree_sum_zero => Physics.AuditMultilinearWeylMass.positive_degree_sum_zero
assert_compatible GUT.AuditMultilinearWeylMass.powerFamily => Physics.AuditMultilinearWeylMass.powerFamily
assert_compatible GUT.AuditMultilinearWeylMass.powerFamily_apply => Physics.AuditMultilinearWeylMass.powerFamily_apply
assert_compatible GUT.AuditMultilinearWeylMass.powerFamily_continuous => Physics.AuditMultilinearWeylMass.powerFamily_continuous
assert_compatible GUT.AuditMultilinearWeylMass.powerFamily_zero => Physics.AuditMultilinearWeylMass.powerFamily_zero
assert_compatible GUT.AuditMultilinearWeylMass.productCoupling => Physics.AuditMultilinearWeylMass.productCoupling
assert_compatible GUT.AuditMultilinearWeylMass.quadraticMass => Physics.AuditMultilinearWeylMass.quadraticMass
assert_compatible GUT.AuditMultilinearWeylMass.quadraticMass.eq_1 => Physics.AuditMultilinearWeylMass.quadraticMass.eq_1
assert_compatible GUT.AuditMultilinearWeylMass.quadraticMass_nonzero => Physics.AuditMultilinearWeylMass.quadraticMass_nonzero
assert_compatible GUT.AuditMultilinearWeylMass.quadratic_not_additive => Physics.AuditMultilinearWeylMass.quadratic_not_additive
assert_compatible GUT.AuditMultilinearWeylMass.trivial => Physics.AuditMultilinearWeylMass.trivial
assert_compatible GUT.AuditMultilinearWeylMass.trivialPair => Physics.AuditMultilinearWeylMass.trivialPair
assert_compatible GUT.AuditMultilinearWeylMass.weight => Physics.AuditMultilinearWeylMass.weight
assert_compatible GUT.WeylMassFamily.EquivariantFamily.atVacuum.eq_1 => Physics.WeylMassFamily.EquivariantFamily.atVacuum.eq_1
