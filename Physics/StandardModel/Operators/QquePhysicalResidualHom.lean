import Physics.StandardModel.Operators.BaryonOne.Qque.QquePhysicalResidualHom
import Physics.StandardModel.Operators.QquePhysicalExteriorCompleteness
import Physics.StandardModel.Operators.QqueCoefficientCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.QquePhysicalResidualHom instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QquePhysicalResidualHom.exists_nonzero_iff => Physics.QquePhysicalResidualHom.exists_nonzero_iff,
  GUT.QquePhysicalResidualHom.homEquiv => Physics.QquePhysicalResidualHom.homEquiv,
  GUT.QquePhysicalResidualHom.legacyEquiv => Physics.QquePhysicalResidualHom.legacyEquiv,
  GUT.QquePhysicalResidualHom.residualIdentification => Physics.QquePhysicalResidualHom.residualIdentification
]

assert_compatible GUT.QquePhysicalResidualHom.exists_nonzero_iff => Physics.QquePhysicalResidualHom.exists_nonzero_iff
assert_compatible GUT.QquePhysicalResidualHom.homEquiv => Physics.QquePhysicalResidualHom.homEquiv
assert_compatible GUT.QquePhysicalResidualHom.legacyEquiv => Physics.QquePhysicalResidualHom.legacyEquiv
assert_compatible GUT.QquePhysicalResidualHom.residualIdentification => Physics.QquePhysicalResidualHom.residualIdentification
