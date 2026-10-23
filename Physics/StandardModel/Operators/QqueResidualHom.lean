import Physics.StandardModel.Operators.BaryonOne.Qque.QqueResidualHom
import Physics.StandardModel.Operators.QqueCoefficientAssembly
import Math.RepresentationTheory.InvariantTensorCurry
import Math.RepresentationTheory.TensorSquareMultilinear
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.QqueResidualHom instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueResidualHom.assembly => Physics.QqueResidualHom.assembly,
  GUT.QqueResidualHom.assembly_injective => Physics.QqueResidualHom.assembly_injective,
  GUT.QqueResidualHom.assembly_nonzero_iff => Physics.QqueResidualHom.assembly_nonzero_iff,
  GUT.QqueResidualHom.equiv => Physics.QqueResidualHom.equiv,
  GUT.QqueResidualHom.equiv_symm_tprod => Physics.QqueResidualHom.equiv_symm_tprod,
  GUT.QqueResidualHom.exists_on_fields => Physics.QqueResidualHom.exists_on_fields,
  GUT.QqueResidualHom.symmetricTensorEquiv => Physics.QqueResidualHom.symmetricTensorEquiv,
  GUT.QqueResidualHom.symmetry_iff => Physics.QqueResidualHom.symmetry_iff,
  GUT.QqueResidualHom.tensorEquiv => Physics.QqueResidualHom.tensorEquiv
]

assert_compatible GUT.QqueResidualHom.assembly => Physics.QqueResidualHom.assembly
assert_compatible GUT.QqueResidualHom.assembly_injective => Physics.QqueResidualHom.assembly_injective
assert_compatible GUT.QqueResidualHom.assembly_nonzero_iff => Physics.QqueResidualHom.assembly_nonzero_iff
assert_compatible GUT.QqueResidualHom.equiv => Physics.QqueResidualHom.equiv
assert_compatible GUT.QqueResidualHom.equiv_symm_tprod => Physics.QqueResidualHom.equiv_symm_tprod
assert_compatible GUT.QqueResidualHom.exists_on_fields => Physics.QqueResidualHom.exists_on_fields
assert_compatible GUT.QqueResidualHom.symmetricTensorEquiv => Physics.QqueResidualHom.symmetricTensorEquiv
assert_compatible GUT.QqueResidualHom.symmetry_iff => Physics.QqueResidualHom.symmetry_iff
assert_compatible GUT.QqueResidualHom.tensorEquiv => Physics.QqueResidualHom.tensorEquiv
