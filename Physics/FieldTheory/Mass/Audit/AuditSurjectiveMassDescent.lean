import Physics.FieldTheory.Mass.Surplus.Audit.AuditSurjectiveMassDescent
import Physics.FieldTheory.Mass.SurjectiveMassDescent
import Physics.FieldTheory.Mass.Audit.AuditAbelianMassSpectrum
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.Audit.AuditSurjectiveMassDescent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AuditAbelianMassSpectrum.imaginaryUnit.eq_1 => Physics.AuditAbelianMassSpectrum.imaginaryUnit.eq_1,
  GUT.AuditSurjectiveMassDescent.collapse => Physics.AuditSurjectiveMassDescent.collapse,
  GUT.AuditSurjectiveMassDescent.collapse.eq_1 => Physics.AuditSurjectiveMassDescent.collapse.eq_1,
  GUT.AuditSurjectiveMassDescent.collapse_not_surjective => Physics.AuditSurjectiveMassDescent.collapse_not_surjective,
  GUT.AuditSurjectiveMassDescent.collapse_spectrum => Physics.AuditSurjectiveMassDescent.collapse_spectrum,
  GUT.AuditSurjectiveMassDescent.coveredMass => Physics.AuditSurjectiveMassDescent.coveredMass,
  GUT.AuditSurjectiveMassDescent.descended_form => Physics.AuditSurjectiveMassDescent.descended_form,
  GUT.AuditSurjectiveMassDescent.descended_nonzero => Physics.AuditSurjectiveMassDescent.descended_nonzero,
  GUT.AuditSurjectiveMassDescent.projected_multiplicity => Physics.AuditSurjectiveMassDescent.projected_multiplicity,
  GUT.AuditSurjectiveMassDescent.projection => Physics.AuditSurjectiveMassDescent.projection,
  GUT.AuditSurjectiveMassDescent.projection_surjective => Physics.AuditSurjectiveMassDescent.projection_surjective
]

assert_compatible GUT.AuditAbelianMassSpectrum.imaginaryUnit.eq_1 => Physics.AuditAbelianMassSpectrum.imaginaryUnit.eq_1
assert_compatible GUT.AuditSurjectiveMassDescent.collapse => Physics.AuditSurjectiveMassDescent.collapse
assert_compatible GUT.AuditSurjectiveMassDescent.collapse.eq_1 => Physics.AuditSurjectiveMassDescent.collapse.eq_1
assert_compatible GUT.AuditSurjectiveMassDescent.collapse_not_surjective => Physics.AuditSurjectiveMassDescent.collapse_not_surjective
assert_compatible GUT.AuditSurjectiveMassDescent.collapse_spectrum => Physics.AuditSurjectiveMassDescent.collapse_spectrum
assert_compatible GUT.AuditSurjectiveMassDescent.coveredMass => Physics.AuditSurjectiveMassDescent.coveredMass
assert_compatible GUT.AuditSurjectiveMassDescent.descended_form => Physics.AuditSurjectiveMassDescent.descended_form
assert_compatible GUT.AuditSurjectiveMassDescent.descended_nonzero => Physics.AuditSurjectiveMassDescent.descended_nonzero
assert_compatible GUT.AuditSurjectiveMassDescent.projected_multiplicity => Physics.AuditSurjectiveMassDescent.projected_multiplicity
assert_compatible GUT.AuditSurjectiveMassDescent.projection => Physics.AuditSurjectiveMassDescent.projection
assert_compatible GUT.AuditSurjectiveMassDescent.projection_surjective => Physics.AuditSurjectiveMassDescent.projection_surjective
