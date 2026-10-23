import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCommutingControl
import Physics.FieldTheory.Jets.WeylHiggsInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCommutingControl instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DerivativeLiteratureMixed.psi.eq_1 => Physics.DerivativeLiteratureMixed.psi.eq_1,
  GUT.WeylHiggsCommutingControl.candidate_zero => Physics.WeylHiggsCommutingControl.candidate_zero,
  GUT.WeylHiggsCommutingControl.current_zero => Physics.WeylHiggsCommutingControl.current_zero,
  GUT.WeylHiggsCommutingControl.odd_zero => Physics.WeylHiggsCommutingControl.odd_zero
]

assert_compatible GUT.DerivativeLiteratureMixed.psi.eq_1 => Physics.DerivativeLiteratureMixed.psi.eq_1
assert_compatible GUT.WeylHiggsCommutingControl.candidate_zero => Physics.WeylHiggsCommutingControl.candidate_zero
assert_compatible GUT.WeylHiggsCommutingControl.current_zero => Physics.WeylHiggsCommutingControl.current_zero
assert_compatible GUT.WeylHiggsCommutingControl.odd_zero => Physics.WeylHiggsCommutingControl.odd_zero
