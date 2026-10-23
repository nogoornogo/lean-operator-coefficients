import Physics.StandardModel.Operators.Selection.ProhibitionInputSM
import Math.RepresentationTheory.ProhibitionInput
import Physics.StandardModel.Operators.KorenSMSelection
import Physics.StandardModel.Operators.BgwZ6Selection
import Physics.StandardModel.Operators.DgtFlavorRestriction
import Physics.StandardModel.Operators.QuarticityAdapters
import Physics.StandardModel.Operators.WeinbergSMInterface
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.ProhibitionInputSM instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ProhibitionInputSM.AllForbids => Physics.ProhibitionInputSM.AllForbids,
  GUT.ProhibitionInputSM.Forbids => Physics.ProhibitionInputSM.Forbids,
  GUT.ProhibitionInputSM.bgw => Physics.ProhibitionInputSM.bgw,
  GUT.ProhibitionInputSM.dgt => Physics.ProhibitionInputSM.dgt,
  GUT.ProhibitionInputSM.dgt_restriction => Physics.ProhibitionInputSM.dgt_restriction,
  GUT.ProhibitionInputSM.facade_iff => Physics.ProhibitionInputSM.facade_iff,
  GUT.ProhibitionInputSM.koren => Physics.ProhibitionInputSM.koren,
  GUT.ProhibitionInputSM.llhh_forbidden_iff => Physics.ProhibitionInputSM.llhh_forbidden_iff,
  GUT.ProhibitionInputSM.quarticity_domains => Physics.ProhibitionInputSM.quarticity_domains,
  GUT.ProhibitionInputSM.residual_iff => Physics.ProhibitionInputSM.residual_iff
]

assert_compatible GUT.ProhibitionInputSM.AllForbids => Physics.ProhibitionInputSM.AllForbids
assert_compatible GUT.ProhibitionInputSM.Forbids => Physics.ProhibitionInputSM.Forbids
assert_compatible GUT.ProhibitionInputSM.bgw => Physics.ProhibitionInputSM.bgw
assert_compatible GUT.ProhibitionInputSM.dgt => Physics.ProhibitionInputSM.dgt
assert_compatible GUT.ProhibitionInputSM.dgt_restriction => Physics.ProhibitionInputSM.dgt_restriction
assert_compatible GUT.ProhibitionInputSM.facade_iff => Physics.ProhibitionInputSM.facade_iff
assert_compatible GUT.ProhibitionInputSM.koren => Physics.ProhibitionInputSM.koren
assert_compatible GUT.ProhibitionInputSM.llhh_forbidden_iff => Physics.ProhibitionInputSM.llhh_forbidden_iff
assert_compatible GUT.ProhibitionInputSM.quarticity_domains => Physics.ProhibitionInputSM.quarticity_domains
assert_compatible GUT.ProhibitionInputSM.residual_iff => Physics.ProhibitionInputSM.residual_iff
