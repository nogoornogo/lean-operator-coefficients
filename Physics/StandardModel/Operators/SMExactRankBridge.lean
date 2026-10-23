import Physics.StandardModel.Operators.Support.Coordinates.SMExactRankBridge
import Math.LinearAlgebra.ExactRankCertificate
import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMExactRankBridge instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMExactRankBridge.rank_from_certificate => Physics.SMExactRankBridge.rank_from_certificate
]

assert_compatible GUT.SMExactRankBridge.rank_from_certificate => Physics.SMExactRankBridge.rank_from_certificate
