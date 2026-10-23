import Physics.StandardModel.Spectrum.Mass.Audit.AuditRestrictedConjugationMassSource
import Physics.StandardModel.Spectrum.ConjugationMassSource
import Physics.StandardModel.Spectrum.Audit.AuditIndependentProfileTotals
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Mass.Audit.AuditRestrictedConjugationMassSource instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.StructuralConjugationMass.AuditRestricted.actual_zeroMode => Physics.StructuralConjugationMass.AuditRestricted.actual_zeroMode,
  GUT.StructuralConjugationMass.AuditRestricted.unequal_target_endpoint => Physics.StructuralConjugationMass.AuditRestricted.unequal_target_endpoint
]

assert_compatible GUT.StructuralConjugationMass.AuditRestricted.actual_zeroMode => Physics.StructuralConjugationMass.AuditRestricted.actual_zeroMode
assert_compatible GUT.StructuralConjugationMass.AuditRestricted.unequal_target_endpoint => Physics.StructuralConjugationMass.AuditRestricted.unequal_target_endpoint
