import Physics.StandardModel.Operators.Support.Lepton.SMLCompactWeyl
import Math.RepresentationTheory.SL2SymmetricSpan
import Physics.StandardModel.Operators.SMConstantSourceCharacter
import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Lepton.SMLCompactWeyl instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMLCompactWeyl.coefficientEquiv => Physics.SMLCompactWeyl.coefficientEquiv,
  GUT.SMLCompactWeyl.coefficient_fixed_iff => Physics.SMLCompactWeyl.coefficient_fixed_iff,
  GUT.SMLCompactWeyl.compactAction => Physics.SMLCompactWeyl.compactAction,
  GUT.SMLCompactWeyl.compactKernelEquiv => Physics.SMLCompactWeyl.compactKernelEquiv,
  GUT.SMLCompactWeyl.compactLocal => Physics.SMLCompactWeyl.compactLocal,
  GUT.SMLCompactWeyl.field_restrict => Physics.SMLCompactWeyl.field_restrict,
  GUT.SMLCompactWeyl.field_spanned => Physics.SMLCompactWeyl.field_spanned,
  GUT.SMLCompactWeyl.higgs_coefficient_fixed_iff => Physics.SMLCompactWeyl.higgs_coefficient_fixed_iff,
  GUT.SMLCompactWeyl.higgs_spanned => Physics.SMLCompactWeyl.higgs_spanned,
  GUT.SMLCompactWeyl.inclusion => Physics.SMLCompactWeyl.inclusion,
  GUT.SMLCompactWeyl.local_coefficient_fixed_iff => Physics.SMLCompactWeyl.local_coefficient_fixed_iff,
  GUT.SMLCompactWeyl.pattern => Physics.SMLCompactWeyl.pattern,
  GUT.SMLCompactWeyl.source => Physics.SMLCompactWeyl.source,
  GUT.SMLCompactWeyl.source_spanned => Physics.SMLCompactWeyl.source_spanned
]

assert_compatible GUT.SMLCompactWeyl.coefficientEquiv => Physics.SMLCompactWeyl.coefficientEquiv
assert_compatible GUT.SMLCompactWeyl.coefficient_fixed_iff => Physics.SMLCompactWeyl.coefficient_fixed_iff
assert_compatible GUT.SMLCompactWeyl.compactAction => Physics.SMLCompactWeyl.compactAction
assert_compatible GUT.SMLCompactWeyl.compactKernelEquiv => Physics.SMLCompactWeyl.compactKernelEquiv
assert_compatible GUT.SMLCompactWeyl.compactLocal => Physics.SMLCompactWeyl.compactLocal
assert_compatible GUT.SMLCompactWeyl.field_restrict => Physics.SMLCompactWeyl.field_restrict
assert_compatible GUT.SMLCompactWeyl.field_spanned => Physics.SMLCompactWeyl.field_spanned
assert_compatible GUT.SMLCompactWeyl.higgs_coefficient_fixed_iff => Physics.SMLCompactWeyl.higgs_coefficient_fixed_iff
assert_compatible GUT.SMLCompactWeyl.higgs_spanned => Physics.SMLCompactWeyl.higgs_spanned
assert_compatible GUT.SMLCompactWeyl.inclusion => Physics.SMLCompactWeyl.inclusion
assert_compatible GUT.SMLCompactWeyl.local_coefficient_fixed_iff => Physics.SMLCompactWeyl.local_coefficient_fixed_iff
assert_compatible GUT.SMLCompactWeyl.pattern => Physics.SMLCompactWeyl.pattern
assert_compatible GUT.SMLCompactWeyl.source => Physics.SMLCompactWeyl.source
assert_compatible GUT.SMLCompactWeyl.source_spanned => Physics.SMLCompactWeyl.source_spanned
