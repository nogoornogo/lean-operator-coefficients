import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneInputTransport
import Physics.StandardModel.Operators.DeltaLOneCoefficientCompleteness
import Math.RepresentationTheory.SpeciesCoefficientTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneInputTransport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaLOneInputTransport.equiv => Physics.DeltaLOneInputTransport.equiv,
  GUT.DeltaLOneInputTransport.equiv_apply => Physics.DeltaLOneInputTransport.equiv_apply,
  GUT.DeltaLOneInputTransport.equiv_symm_apply => Physics.DeltaLOneInputTransport.equiv_symm_apply,
  GUT.DeltaLOneInputTransport.fieldsEquiv => Physics.DeltaLOneInputTransport.fieldsEquiv,
  GUT.DeltaLOneInputTransport.fieldsEquiv_single => Physics.DeltaLOneInputTransport.fieldsEquiv_single,
  GUT.DeltaLOneInputTransport.onFieldsEquiv => Physics.DeltaLOneInputTransport.onFieldsEquiv,
  GUT.DeltaLOneInputTransport.pull => Physics.DeltaLOneInputTransport.pull,
  GUT.DeltaLOneInputTransport.pull_mem => Physics.DeltaLOneInputTransport.pull_mem,
  GUT.DeltaLOneInputTransport.pull_symm => Physics.DeltaLOneInputTransport.pull_symm
]

assert_compatible GUT.DeltaLOneInputTransport.equiv => Physics.DeltaLOneInputTransport.equiv
assert_compatible GUT.DeltaLOneInputTransport.equiv_apply => Physics.DeltaLOneInputTransport.equiv_apply
assert_compatible GUT.DeltaLOneInputTransport.equiv_symm_apply => Physics.DeltaLOneInputTransport.equiv_symm_apply
assert_compatible GUT.DeltaLOneInputTransport.fieldsEquiv => Physics.DeltaLOneInputTransport.fieldsEquiv
assert_compatible GUT.DeltaLOneInputTransport.fieldsEquiv_single => Physics.DeltaLOneInputTransport.fieldsEquiv_single
assert_compatible GUT.DeltaLOneInputTransport.onFieldsEquiv => Physics.DeltaLOneInputTransport.onFieldsEquiv
assert_compatible GUT.DeltaLOneInputTransport.pull => Physics.DeltaLOneInputTransport.pull
assert_compatible GUT.DeltaLOneInputTransport.pull_mem => Physics.DeltaLOneInputTransport.pull_mem
assert_compatible GUT.DeltaLOneInputTransport.pull_symm => Physics.DeltaLOneInputTransport.pull_symm
