import Physics.StandardModel.Spectrum.Representations.Audit.AuditTwoConjugationQque
import Physics.StandardModel.Spectrum.TwoConjugationQque
import Physics.StandardModel.Spectrum.ConjugationTrialityObstruction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.Audit.AuditTwoConjugationQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.TwoConjugationControls.triality_no_two => Physics.TwoConjugationControls.triality_no_two
]

assert_compatible GUT.TwoConjugationControls.triality_no_two => Physics.TwoConjugationControls.triality_no_two
