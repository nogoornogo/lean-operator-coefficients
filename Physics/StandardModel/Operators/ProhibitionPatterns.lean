import Physics.StandardModel.Operators.Selection.ProhibitionPatterns
import Physics.StandardModel.Operators.ProhibitionInputSM
import Math.RepresentationTheory.ProhibitionPatterns
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.ProhibitionPatterns instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.KorenSMSelection.target.eq_1 => Physics.KorenSMSelection.target.eq_1,
  GUT.ProhibitionPatterns.BLTarget => Physics.ProhibitionPatterns.BLTarget,
  GUT.ProhibitionPatterns.BLTarget.bOne => Physics.ProhibitionPatterns.BLTarget.bOne,
  GUT.ProhibitionPatterns.BLTarget.bOne.elim => Physics.ProhibitionPatterns.BLTarget.bOne.elim,
  GUT.ProhibitionPatterns.BLTarget.bOne.sizeOf_spec => Physics.ProhibitionPatterns.BLTarget.bOne.sizeOf_spec,
  GUT.ProhibitionPatterns.BLTarget.bTwo => Physics.ProhibitionPatterns.BLTarget.bTwo,
  GUT.ProhibitionPatterns.BLTarget.bTwo.elim => Physics.ProhibitionPatterns.BLTarget.bTwo.elim,
  GUT.ProhibitionPatterns.BLTarget.bTwo.sizeOf_spec => Physics.ProhibitionPatterns.BLTarget.bTwo.sizeOf_spec,
  GUT.ProhibitionPatterns.BLTarget.casesOn => Physics.ProhibitionPatterns.BLTarget.casesOn,
  GUT.ProhibitionPatterns.BLTarget.ctorElim => Physics.ProhibitionPatterns.BLTarget.ctorElim,
  GUT.ProhibitionPatterns.BLTarget.ctorElimType => Physics.ProhibitionPatterns.BLTarget.ctorElimType,
  GUT.ProhibitionPatterns.BLTarget.ctorIdx => Physics.ProhibitionPatterns.BLTarget.ctorIdx,
  GUT.ProhibitionPatterns.BLTarget.lTwo => Physics.ProhibitionPatterns.BLTarget.lTwo,
  GUT.ProhibitionPatterns.BLTarget.lTwo.elim => Physics.ProhibitionPatterns.BLTarget.lTwo.elim,
  GUT.ProhibitionPatterns.BLTarget.lTwo.sizeOf_spec => Physics.ProhibitionPatterns.BLTarget.lTwo.sizeOf_spec,
  GUT.ProhibitionPatterns.BLTarget.noConfusion => Physics.ProhibitionPatterns.BLTarget.noConfusion,
  GUT.ProhibitionPatterns.BLTarget.noConfusionType => Physics.ProhibitionPatterns.BLTarget.noConfusionType,
  GUT.ProhibitionPatterns.BLTarget.ofNat => Physics.ProhibitionPatterns.BLTarget.ofNat,
  GUT.ProhibitionPatterns.BLTarget.ofNat_ctorIdx => Physics.ProhibitionPatterns.BLTarget.ofNat_ctorIdx,
  GUT.ProhibitionPatterns.BLTarget.rec => Physics.ProhibitionPatterns.BLTarget.rec,
  GUT.ProhibitionPatterns.BLTarget.recOn => Physics.ProhibitionPatterns.BLTarget.recOn,
  GUT.ProhibitionPatterns.ForbidsChosen => Physics.ProhibitionPatterns.ForbidsChosen,
  GUT.ProhibitionPatterns.JointForbids => Physics.ProhibitionPatterns.JointForbids,
  GUT.ProhibitionPatterns.baryonTargets => Physics.ProhibitionPatterns.baryonTargets,
  GUT.ProhibitionPatterns.bgw_baryon => Physics.ProhibitionPatterns.bgw_baryon,
  GUT.ProhibitionPatterns.chosen_iff => Physics.ProhibitionPatterns.chosen_iff,
  GUT.ProhibitionPatterns.dgt_joint => Physics.ProhibitionPatterns.dgt_joint,
  GUT.ProhibitionPatterns.dgt_uv_baryon => Physics.ProhibitionPatterns.dgt_uv_baryon,
  GUT.ProhibitionPatterns.empty_chosen => Physics.ProhibitionPatterns.empty_chosen,
  GUT.ProhibitionPatterns.instDecidableEqBLTarget => Physics.ProhibitionPatterns.instDecidableEqBLTarget,
  GUT.ProhibitionPatterns.joint_iff => Physics.ProhibitionPatterns.joint_iff,
  GUT.ProhibitionPatterns.koren_chosen => Physics.ProhibitionPatterns.koren_chosen,
  GUT.ProhibitionPatterns.request => Physics.ProhibitionPatterns.request,
  GUT.ProhibitionPatterns.specification => Physics.ProhibitionPatterns.specification,
  GUT.ProhibitionPatterns.target => Physics.ProhibitionPatterns.target,
  GUT.ProhibitionPatterns.target.eq_1 => Physics.ProhibitionPatterns.target.eq_1,
  GUT.ProhibitionPatterns.target.eq_2 => Physics.ProhibitionPatterns.target.eq_2,
  GUT.ProhibitionPatterns.target.eq_3 => Physics.ProhibitionPatterns.target.eq_3,
  GUT.ProhibitionPatterns.triple_iff => Physics.ProhibitionPatterns.triple_iff
]

assert_compatible GUT.KorenSMSelection.target.eq_1 => Physics.KorenSMSelection.target.eq_1
assert_compatible GUT.ProhibitionPatterns.BLTarget => Physics.ProhibitionPatterns.BLTarget
assert_compatible GUT.ProhibitionPatterns.BLTarget.bOne => Physics.ProhibitionPatterns.BLTarget.bOne
assert_compatible GUT.ProhibitionPatterns.BLTarget.bOne.elim => Physics.ProhibitionPatterns.BLTarget.bOne.elim
assert_compatible GUT.ProhibitionPatterns.BLTarget.bOne.sizeOf_spec => Physics.ProhibitionPatterns.BLTarget.bOne.sizeOf_spec
assert_compatible GUT.ProhibitionPatterns.BLTarget.bTwo => Physics.ProhibitionPatterns.BLTarget.bTwo
assert_compatible GUT.ProhibitionPatterns.BLTarget.bTwo.elim => Physics.ProhibitionPatterns.BLTarget.bTwo.elim
assert_compatible GUT.ProhibitionPatterns.BLTarget.bTwo.sizeOf_spec => Physics.ProhibitionPatterns.BLTarget.bTwo.sizeOf_spec
assert_compatible GUT.ProhibitionPatterns.BLTarget.casesOn => Physics.ProhibitionPatterns.BLTarget.casesOn
assert_compatible GUT.ProhibitionPatterns.BLTarget.ctorElim => Physics.ProhibitionPatterns.BLTarget.ctorElim
assert_compatible GUT.ProhibitionPatterns.BLTarget.ctorElimType => Physics.ProhibitionPatterns.BLTarget.ctorElimType
assert_compatible GUT.ProhibitionPatterns.BLTarget.ctorIdx => Physics.ProhibitionPatterns.BLTarget.ctorIdx
assert_compatible GUT.ProhibitionPatterns.BLTarget.lTwo => Physics.ProhibitionPatterns.BLTarget.lTwo
assert_compatible GUT.ProhibitionPatterns.BLTarget.lTwo.elim => Physics.ProhibitionPatterns.BLTarget.lTwo.elim
assert_compatible GUT.ProhibitionPatterns.BLTarget.lTwo.sizeOf_spec => Physics.ProhibitionPatterns.BLTarget.lTwo.sizeOf_spec
assert_compatible GUT.ProhibitionPatterns.BLTarget.noConfusion => Physics.ProhibitionPatterns.BLTarget.noConfusion
assert_compatible GUT.ProhibitionPatterns.BLTarget.noConfusionType => Physics.ProhibitionPatterns.BLTarget.noConfusionType
assert_compatible GUT.ProhibitionPatterns.BLTarget.ofNat => Physics.ProhibitionPatterns.BLTarget.ofNat
assert_compatible GUT.ProhibitionPatterns.BLTarget.ofNat_ctorIdx => Physics.ProhibitionPatterns.BLTarget.ofNat_ctorIdx
assert_compatible GUT.ProhibitionPatterns.BLTarget.rec => Physics.ProhibitionPatterns.BLTarget.rec
assert_compatible GUT.ProhibitionPatterns.BLTarget.recOn => Physics.ProhibitionPatterns.BLTarget.recOn
assert_compatible GUT.ProhibitionPatterns.ForbidsChosen => Physics.ProhibitionPatterns.ForbidsChosen
assert_compatible GUT.ProhibitionPatterns.JointForbids => Physics.ProhibitionPatterns.JointForbids
assert_compatible GUT.ProhibitionPatterns.baryonTargets => Physics.ProhibitionPatterns.baryonTargets
assert_compatible GUT.ProhibitionPatterns.bgw_baryon => Physics.ProhibitionPatterns.bgw_baryon
assert_compatible GUT.ProhibitionPatterns.chosen_iff => Physics.ProhibitionPatterns.chosen_iff
assert_compatible GUT.ProhibitionPatterns.dgt_joint => Physics.ProhibitionPatterns.dgt_joint
assert_compatible GUT.ProhibitionPatterns.dgt_uv_baryon => Physics.ProhibitionPatterns.dgt_uv_baryon
assert_compatible GUT.ProhibitionPatterns.empty_chosen => Physics.ProhibitionPatterns.empty_chosen
assert_compatible GUT.ProhibitionPatterns.instDecidableEqBLTarget => Physics.ProhibitionPatterns.instDecidableEqBLTarget
assert_compatible GUT.ProhibitionPatterns.joint_iff => Physics.ProhibitionPatterns.joint_iff
assert_compatible GUT.ProhibitionPatterns.koren_chosen => Physics.ProhibitionPatterns.koren_chosen
assert_compatible GUT.ProhibitionPatterns.request => Physics.ProhibitionPatterns.request
assert_compatible GUT.ProhibitionPatterns.specification => Physics.ProhibitionPatterns.specification
assert_compatible GUT.ProhibitionPatterns.target => Physics.ProhibitionPatterns.target
assert_compatible GUT.ProhibitionPatterns.target.eq_1 => Physics.ProhibitionPatterns.target.eq_1
assert_compatible GUT.ProhibitionPatterns.target.eq_2 => Physics.ProhibitionPatterns.target.eq_2
assert_compatible GUT.ProhibitionPatterns.target.eq_3 => Physics.ProhibitionPatterns.target.eq_3
assert_compatible GUT.ProhibitionPatterns.triple_iff => Physics.ProhibitionPatterns.triple_iff
