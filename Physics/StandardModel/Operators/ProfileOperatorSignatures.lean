import Physics.StandardModel.Operators.Selection.ProfileOperatorSignatures
import Physics.StandardModel.Spectrum.FiniteChargeProfiles
import Physics.StandardModel.Operators.StandardModelLocalOperator
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.ProfileOperatorSignatures instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FiniteChargeProfiles.exists_supported_signature_pair => Physics.FiniteChargeProfiles.exists_supported_signature_pair
]

assert_compatible GUT.FiniteChargeProfiles.exists_supported_signature_pair => Physics.FiniteChargeProfiles.exists_supported_signature_pair
