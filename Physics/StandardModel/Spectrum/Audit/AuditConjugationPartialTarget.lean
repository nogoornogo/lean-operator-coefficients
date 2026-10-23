import Physics.StandardModel.Spectrum.Representations.Audit.AuditConjugationPartialTarget
import Physics.StandardModel.Spectrum.ConjugationPartialTarget
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.Audit.AuditConjugationPartialTarget instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ConjugationPartialTarget.Audit.actual_zeroMode => Physics.ConjugationPartialTarget.Audit.actual_zeroMode,
  GUT.ConjugationPartialTarget.Audit.recover_full_target => Physics.ConjugationPartialTarget.Audit.recover_full_target
]

assert_compatible GUT.ConjugationPartialTarget.Audit.actual_zeroMode => Physics.ConjugationPartialTarget.Audit.actual_zeroMode
assert_compatible GUT.ConjugationPartialTarget.Audit.recover_full_target => Physics.ConjugationPartialTarget.Audit.recover_full_target
