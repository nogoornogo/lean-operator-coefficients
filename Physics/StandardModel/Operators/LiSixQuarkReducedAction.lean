import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkReducedAction
import Physics.StandardModel.Operators.LiSixQuarkSeedRecipe
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkReducedAction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkReducedAction.colorAssemble => Physics.LiSixQuarkReducedAction.colorAssemble,
  GUT.LiSixQuarkReducedAction.colorAssemble.eq_1 => Physics.LiSixQuarkReducedAction.colorAssemble.eq_1,
  GUT.LiSixQuarkReducedAction.colorExtract => Physics.LiSixQuarkReducedAction.colorExtract,
  GUT.LiSixQuarkReducedAction.colorExtract.eq_1 => Physics.LiSixQuarkReducedAction.colorExtract.eq_1,
  GUT.LiSixQuarkReducedAction.colorReduced => Physics.LiSixQuarkReducedAction.colorReduced,
  GUT.LiSixQuarkReducedAction.colorReduced.eq_1 => Physics.LiSixQuarkReducedAction.colorReduced.eq_1,
  GUT.LiSixQuarkReducedAction.colorReduced.eq_2 => Physics.LiSixQuarkReducedAction.colorReduced.eq_2,
  GUT.LiSixQuarkReducedAction.colorReduced.eq_3 => Physics.LiSixQuarkReducedAction.colorReduced.eq_3,
  GUT.LiSixQuarkReducedAction.colorReduced.eq_4 => Physics.LiSixQuarkReducedAction.colorReduced.eq_4,
  GUT.LiSixQuarkReducedAction.color_injective => Physics.LiSixQuarkReducedAction.color_injective,
  GUT.LiSixQuarkReducedAction.color_intertwine => Physics.LiSixQuarkReducedAction.color_intertwine,
  GUT.LiSixQuarkReducedAction.color_left_inverse => Physics.LiSixQuarkReducedAction.color_left_inverse,
  GUT.LiSixQuarkReducedAction.extractColor => Physics.LiSixQuarkReducedAction.extractColor,
  GUT.LiSixQuarkReducedAction.extractSpin => Physics.LiSixQuarkReducedAction.extractSpin,
  GUT.LiSixQuarkReducedAction.extraction => Physics.LiSixQuarkReducedAction.extraction,
  GUT.LiSixQuarkReducedAction.extraction_action => Physics.LiSixQuarkReducedAction.extraction_action,
  GUT.LiSixQuarkReducedAction.extraction_injective => Physics.LiSixQuarkReducedAction.extraction_injective,
  GUT.LiSixQuarkReducedAction.extraction_word => Physics.LiSixQuarkReducedAction.extraction_word,
  GUT.LiSixQuarkReducedAction.extraction_young => Physics.LiSixQuarkReducedAction.extraction_young,
  GUT.LiSixQuarkReducedAction.reducedAction => Physics.LiSixQuarkReducedAction.reducedAction,
  GUT.LiSixQuarkReducedAction.reducedAction_apply => Physics.LiSixQuarkReducedAction.reducedAction_apply,
  GUT.LiSixQuarkReducedAction.reducedColor => Physics.LiSixQuarkReducedAction.reducedColor,
  GUT.LiSixQuarkReducedAction.reducedSpin => Physics.LiSixQuarkReducedAction.reducedSpin,
  GUT.LiSixQuarkReducedAction.row_column_commute => Physics.LiSixQuarkReducedAction.row_column_commute,
  GUT.LiSixQuarkReducedAction.spinAssemble => Physics.LiSixQuarkReducedAction.spinAssemble,
  GUT.LiSixQuarkReducedAction.spinAssemble.eq_1 => Physics.LiSixQuarkReducedAction.spinAssemble.eq_1,
  GUT.LiSixQuarkReducedAction.spinExtract => Physics.LiSixQuarkReducedAction.spinExtract,
  GUT.LiSixQuarkReducedAction.spinExtract.eq_1 => Physics.LiSixQuarkReducedAction.spinExtract.eq_1,
  GUT.LiSixQuarkReducedAction.spinReduced => Physics.LiSixQuarkReducedAction.spinReduced,
  GUT.LiSixQuarkReducedAction.spinReduced.eq_1 => Physics.LiSixQuarkReducedAction.spinReduced.eq_1,
  GUT.LiSixQuarkReducedAction.spinReduced.eq_2 => Physics.LiSixQuarkReducedAction.spinReduced.eq_2,
  GUT.LiSixQuarkReducedAction.spinReduced.eq_3 => Physics.LiSixQuarkReducedAction.spinReduced.eq_3,
  GUT.LiSixQuarkReducedAction.spinReduced.eq_4 => Physics.LiSixQuarkReducedAction.spinReduced.eq_4,
  GUT.LiSixQuarkReducedAction.spin_injective => Physics.LiSixQuarkReducedAction.spin_injective,
  GUT.LiSixQuarkReducedAction.spin_intertwine => Physics.LiSixQuarkReducedAction.spin_intertwine,
  GUT.LiSixQuarkReducedAction.spin_left_inverse => Physics.LiSixQuarkReducedAction.spin_left_inverse
]

assert_compatible GUT.LiSixQuarkReducedAction.colorAssemble => Physics.LiSixQuarkReducedAction.colorAssemble
assert_compatible GUT.LiSixQuarkReducedAction.colorAssemble.eq_1 => Physics.LiSixQuarkReducedAction.colorAssemble.eq_1
assert_compatible GUT.LiSixQuarkReducedAction.colorExtract => Physics.LiSixQuarkReducedAction.colorExtract
assert_compatible GUT.LiSixQuarkReducedAction.colorExtract.eq_1 => Physics.LiSixQuarkReducedAction.colorExtract.eq_1
assert_compatible GUT.LiSixQuarkReducedAction.colorReduced => Physics.LiSixQuarkReducedAction.colorReduced
assert_compatible GUT.LiSixQuarkReducedAction.colorReduced.eq_1 => Physics.LiSixQuarkReducedAction.colorReduced.eq_1
assert_compatible GUT.LiSixQuarkReducedAction.colorReduced.eq_2 => Physics.LiSixQuarkReducedAction.colorReduced.eq_2
assert_compatible GUT.LiSixQuarkReducedAction.colorReduced.eq_3 => Physics.LiSixQuarkReducedAction.colorReduced.eq_3
assert_compatible GUT.LiSixQuarkReducedAction.colorReduced.eq_4 => Physics.LiSixQuarkReducedAction.colorReduced.eq_4
assert_compatible GUT.LiSixQuarkReducedAction.color_injective => Physics.LiSixQuarkReducedAction.color_injective
assert_compatible GUT.LiSixQuarkReducedAction.color_intertwine => Physics.LiSixQuarkReducedAction.color_intertwine
assert_compatible GUT.LiSixQuarkReducedAction.color_left_inverse => Physics.LiSixQuarkReducedAction.color_left_inverse
assert_compatible GUT.LiSixQuarkReducedAction.extractColor => Physics.LiSixQuarkReducedAction.extractColor
assert_compatible GUT.LiSixQuarkReducedAction.extractSpin => Physics.LiSixQuarkReducedAction.extractSpin
assert_compatible GUT.LiSixQuarkReducedAction.extraction => Physics.LiSixQuarkReducedAction.extraction
assert_compatible GUT.LiSixQuarkReducedAction.extraction_action => Physics.LiSixQuarkReducedAction.extraction_action
assert_compatible GUT.LiSixQuarkReducedAction.extraction_injective => Physics.LiSixQuarkReducedAction.extraction_injective
assert_compatible GUT.LiSixQuarkReducedAction.extraction_word => Physics.LiSixQuarkReducedAction.extraction_word
assert_compatible GUT.LiSixQuarkReducedAction.extraction_young => Physics.LiSixQuarkReducedAction.extraction_young
assert_compatible GUT.LiSixQuarkReducedAction.reducedAction => Physics.LiSixQuarkReducedAction.reducedAction
assert_compatible GUT.LiSixQuarkReducedAction.reducedAction_apply => Physics.LiSixQuarkReducedAction.reducedAction_apply
assert_compatible GUT.LiSixQuarkReducedAction.reducedColor => Physics.LiSixQuarkReducedAction.reducedColor
assert_compatible GUT.LiSixQuarkReducedAction.reducedSpin => Physics.LiSixQuarkReducedAction.reducedSpin
assert_compatible GUT.LiSixQuarkReducedAction.row_column_commute => Physics.LiSixQuarkReducedAction.row_column_commute
assert_compatible GUT.LiSixQuarkReducedAction.spinAssemble => Physics.LiSixQuarkReducedAction.spinAssemble
assert_compatible GUT.LiSixQuarkReducedAction.spinAssemble.eq_1 => Physics.LiSixQuarkReducedAction.spinAssemble.eq_1
assert_compatible GUT.LiSixQuarkReducedAction.spinExtract => Physics.LiSixQuarkReducedAction.spinExtract
assert_compatible GUT.LiSixQuarkReducedAction.spinExtract.eq_1 => Physics.LiSixQuarkReducedAction.spinExtract.eq_1
assert_compatible GUT.LiSixQuarkReducedAction.spinReduced => Physics.LiSixQuarkReducedAction.spinReduced
assert_compatible GUT.LiSixQuarkReducedAction.spinReduced.eq_1 => Physics.LiSixQuarkReducedAction.spinReduced.eq_1
assert_compatible GUT.LiSixQuarkReducedAction.spinReduced.eq_2 => Physics.LiSixQuarkReducedAction.spinReduced.eq_2
assert_compatible GUT.LiSixQuarkReducedAction.spinReduced.eq_3 => Physics.LiSixQuarkReducedAction.spinReduced.eq_3
assert_compatible GUT.LiSixQuarkReducedAction.spinReduced.eq_4 => Physics.LiSixQuarkReducedAction.spinReduced.eq_4
assert_compatible GUT.LiSixQuarkReducedAction.spin_injective => Physics.LiSixQuarkReducedAction.spin_injective
assert_compatible GUT.LiSixQuarkReducedAction.spin_intertwine => Physics.LiSixQuarkReducedAction.spin_intertwine
assert_compatible GUT.LiSixQuarkReducedAction.spin_left_inverse => Physics.LiSixQuarkReducedAction.spin_left_inverse
