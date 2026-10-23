import Physics.StandardModel.Operators.Selection.MixedSelectionPatterns
import Math.LinearAlgebra.MixedSelectionRequests
import Physics.StandardModel.Operators.ProhibitionPatterns
import Physics.StandardModel.Operators.BgwChargedHiggsWeinberg
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.MixedSelectionPatterns instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.MixedSelectionPatterns.BgwTarget => Physics.MixedSelectionPatterns.BgwTarget,
  GUT.MixedSelectionPatterns.BgwTarget.bOne => Physics.MixedSelectionPatterns.BgwTarget.bOne,
  GUT.MixedSelectionPatterns.BgwTarget.bOne.elim => Physics.MixedSelectionPatterns.BgwTarget.bOne.elim,
  GUT.MixedSelectionPatterns.BgwTarget.bOne.sizeOf_spec => Physics.MixedSelectionPatterns.BgwTarget.bOne.sizeOf_spec,
  GUT.MixedSelectionPatterns.BgwTarget.bTwo => Physics.MixedSelectionPatterns.BgwTarget.bTwo,
  GUT.MixedSelectionPatterns.BgwTarget.bTwo.elim => Physics.MixedSelectionPatterns.BgwTarget.bTwo.elim,
  GUT.MixedSelectionPatterns.BgwTarget.bTwo.sizeOf_spec => Physics.MixedSelectionPatterns.BgwTarget.bTwo.sizeOf_spec,
  GUT.MixedSelectionPatterns.BgwTarget.casesOn => Physics.MixedSelectionPatterns.BgwTarget.casesOn,
  GUT.MixedSelectionPatterns.BgwTarget.ctorElim => Physics.MixedSelectionPatterns.BgwTarget.ctorElim,
  GUT.MixedSelectionPatterns.BgwTarget.ctorElimType => Physics.MixedSelectionPatterns.BgwTarget.ctorElimType,
  GUT.MixedSelectionPatterns.BgwTarget.ctorIdx => Physics.MixedSelectionPatterns.BgwTarget.ctorIdx,
  GUT.MixedSelectionPatterns.BgwTarget.llhh => Physics.MixedSelectionPatterns.BgwTarget.llhh,
  GUT.MixedSelectionPatterns.BgwTarget.llhh.elim => Physics.MixedSelectionPatterns.BgwTarget.llhh.elim,
  GUT.MixedSelectionPatterns.BgwTarget.llhh.sizeOf_spec => Physics.MixedSelectionPatterns.BgwTarget.llhh.sizeOf_spec,
  GUT.MixedSelectionPatterns.BgwTarget.noConfusion => Physics.MixedSelectionPatterns.BgwTarget.noConfusion,
  GUT.MixedSelectionPatterns.BgwTarget.noConfusionType => Physics.MixedSelectionPatterns.BgwTarget.noConfusionType,
  GUT.MixedSelectionPatterns.BgwTarget.ofNat => Physics.MixedSelectionPatterns.BgwTarget.ofNat,
  GUT.MixedSelectionPatterns.BgwTarget.ofNat_ctorIdx => Physics.MixedSelectionPatterns.BgwTarget.ofNat_ctorIdx,
  GUT.MixedSelectionPatterns.BgwTarget.rec => Physics.MixedSelectionPatterns.BgwTarget.rec,
  GUT.MixedSelectionPatterns.BgwTarget.recOn => Physics.MixedSelectionPatterns.BgwTarget.recOn,
  GUT.MixedSelectionPatterns.bgwDomain => Physics.MixedSelectionPatterns.bgwDomain,
  GUT.MixedSelectionPatterns.bgwRequest => Physics.MixedSelectionPatterns.bgwRequest,
  GUT.MixedSelectionPatterns.bgw_components => Physics.MixedSelectionPatterns.bgw_components,
  GUT.MixedSelectionPatterns.bgw_domain_forbidden_iff => Physics.MixedSelectionPatterns.bgw_domain_forbidden_iff,
  GUT.MixedSelectionPatterns.bgw_satisfies => Physics.MixedSelectionPatterns.bgw_satisfies,
  GUT.MixedSelectionPatterns.dgt_selected_allowed => Physics.MixedSelectionPatterns.dgt_selected_allowed,
  GUT.MixedSelectionPatterns.dgt_selector_range_allowed => Physics.MixedSelectionPatterns.dgt_selector_range_allowed,
  GUT.MixedSelectionPatterns.instDecidableEqBgwTarget => Physics.MixedSelectionPatterns.instDecidableEqBgwTarget,
  GUT.MixedSelectionPatterns.instZeroBgwDomain => Physics.MixedSelectionPatterns.instZeroBgwDomain
]

assert_compatible GUT.MixedSelectionPatterns.BgwTarget => Physics.MixedSelectionPatterns.BgwTarget
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.bOne => Physics.MixedSelectionPatterns.BgwTarget.bOne
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.bOne.elim => Physics.MixedSelectionPatterns.BgwTarget.bOne.elim
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.bOne.sizeOf_spec => Physics.MixedSelectionPatterns.BgwTarget.bOne.sizeOf_spec
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.bTwo => Physics.MixedSelectionPatterns.BgwTarget.bTwo
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.bTwo.elim => Physics.MixedSelectionPatterns.BgwTarget.bTwo.elim
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.bTwo.sizeOf_spec => Physics.MixedSelectionPatterns.BgwTarget.bTwo.sizeOf_spec
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.casesOn => Physics.MixedSelectionPatterns.BgwTarget.casesOn
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.ctorElim => Physics.MixedSelectionPatterns.BgwTarget.ctorElim
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.ctorElimType => Physics.MixedSelectionPatterns.BgwTarget.ctorElimType
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.ctorIdx => Physics.MixedSelectionPatterns.BgwTarget.ctorIdx
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.llhh => Physics.MixedSelectionPatterns.BgwTarget.llhh
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.llhh.elim => Physics.MixedSelectionPatterns.BgwTarget.llhh.elim
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.llhh.sizeOf_spec => Physics.MixedSelectionPatterns.BgwTarget.llhh.sizeOf_spec
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.noConfusion => Physics.MixedSelectionPatterns.BgwTarget.noConfusion
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.noConfusionType => Physics.MixedSelectionPatterns.BgwTarget.noConfusionType
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.ofNat => Physics.MixedSelectionPatterns.BgwTarget.ofNat
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.ofNat_ctorIdx => Physics.MixedSelectionPatterns.BgwTarget.ofNat_ctorIdx
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.rec => Physics.MixedSelectionPatterns.BgwTarget.rec
assert_compatible GUT.MixedSelectionPatterns.BgwTarget.recOn => Physics.MixedSelectionPatterns.BgwTarget.recOn
assert_compatible GUT.MixedSelectionPatterns.bgwDomain => Physics.MixedSelectionPatterns.bgwDomain
assert_compatible GUT.MixedSelectionPatterns.bgwRequest => Physics.MixedSelectionPatterns.bgwRequest
assert_compatible GUT.MixedSelectionPatterns.bgw_components => Physics.MixedSelectionPatterns.bgw_components
assert_compatible GUT.MixedSelectionPatterns.bgw_domain_forbidden_iff => Physics.MixedSelectionPatterns.bgw_domain_forbidden_iff
assert_compatible GUT.MixedSelectionPatterns.bgw_satisfies => Physics.MixedSelectionPatterns.bgw_satisfies
assert_compatible GUT.MixedSelectionPatterns.dgt_selected_allowed => Physics.MixedSelectionPatterns.dgt_selected_allowed
assert_compatible GUT.MixedSelectionPatterns.dgt_selector_range_allowed => Physics.MixedSelectionPatterns.dgt_selector_range_allowed
assert_compatible GUT.MixedSelectionPatterns.instDecidableEqBgwTarget => Physics.MixedSelectionPatterns.instDecidableEqBgwTarget
assert_compatible GUT.MixedSelectionPatterns.instZeroBgwDomain => Physics.MixedSelectionPatterns.instZeroBgwDomain
