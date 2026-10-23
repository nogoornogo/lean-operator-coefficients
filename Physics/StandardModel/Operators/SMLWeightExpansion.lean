import Physics.StandardModel.Operators.Support.Lepton.SMLWeightExpansion
import Physics.StandardModel.Operators.SMConstantSourceCharacter
import Physics.StandardModel.Operators.SMLCompactWeyl
import Math.RepresentationTheory.SU2SignedWeights
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Lepton.SMLWeightExpansion instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMConstantSourceCharacter.leptonTorus.eq_1 => Physics.SMConstantSourceCharacter.leptonTorus.eq_1,
  GUT.SMLWeightExpansion.Indices => Physics.SMLWeightExpansion.Indices,
  GUT.SMLWeightExpansion.Slots => Physics.SMLWeightExpansion.Slots,
  GUT.SMLWeightExpansion.Subsets => Physics.SMLWeightExpansion.Subsets,
  GUT.SMLWeightExpansion.action => Physics.SMLWeightExpansion.action,
  GUT.SMLWeightExpansion.fieldFinite => Physics.SMLWeightExpansion.fieldFinite,
  GUT.SMLWeightExpansion.pairInclusion => Physics.SMLWeightExpansion.pairInclusion,
  GUT.SMLWeightExpansion.prod_zpow => Physics.SMLWeightExpansion.prod_zpow,
  GUT.SMLWeightExpansion.sourceFinite => Physics.SMLWeightExpansion.sourceFinite,
  GUT.SMLWeightExpansion.source_character => Physics.SMLWeightExpansion.source_character,
  GUT.SMLWeightExpansion.spinWeight => Physics.SMLWeightExpansion.spinWeight,
  GUT.SMLWeightExpansion.torus_character => Physics.SMLWeightExpansion.torus_character,
  GUT.SMLWeightExpansion.totalSpin => Physics.SMLWeightExpansion.totalSpin,
  GUT.SMLWeightExpansion.totalSpin.eq_1 => Physics.SMLWeightExpansion.totalSpin.eq_1,
  GUT.SMLWeightExpansion.totalWeak => Physics.SMLWeightExpansion.totalWeak,
  GUT.SMLWeightExpansion.totalWeak.eq_1 => Physics.SMLWeightExpansion.totalWeak.eq_1,
  GUT.SMLWeightExpansion.weakWeight => Physics.SMLWeightExpansion.weakWeight
]

assert_compatible GUT.SMConstantSourceCharacter.leptonTorus.eq_1 => Physics.SMConstantSourceCharacter.leptonTorus.eq_1
assert_compatible GUT.SMLWeightExpansion.Indices => Physics.SMLWeightExpansion.Indices
assert_compatible GUT.SMLWeightExpansion.Slots => Physics.SMLWeightExpansion.Slots
assert_compatible GUT.SMLWeightExpansion.Subsets => Physics.SMLWeightExpansion.Subsets
assert_compatible GUT.SMLWeightExpansion.action => Physics.SMLWeightExpansion.action
assert_compatible GUT.SMLWeightExpansion.fieldFinite => Physics.SMLWeightExpansion.fieldFinite
assert_compatible GUT.SMLWeightExpansion.pairInclusion => Physics.SMLWeightExpansion.pairInclusion
assert_compatible GUT.SMLWeightExpansion.prod_zpow => Physics.SMLWeightExpansion.prod_zpow
assert_compatible GUT.SMLWeightExpansion.sourceFinite => Physics.SMLWeightExpansion.sourceFinite
assert_compatible GUT.SMLWeightExpansion.source_character => Physics.SMLWeightExpansion.source_character
assert_compatible GUT.SMLWeightExpansion.spinWeight => Physics.SMLWeightExpansion.spinWeight
assert_compatible GUT.SMLWeightExpansion.torus_character => Physics.SMLWeightExpansion.torus_character
assert_compatible GUT.SMLWeightExpansion.totalSpin => Physics.SMLWeightExpansion.totalSpin
assert_compatible GUT.SMLWeightExpansion.totalSpin.eq_1 => Physics.SMLWeightExpansion.totalSpin.eq_1
assert_compatible GUT.SMLWeightExpansion.totalWeak => Physics.SMLWeightExpansion.totalWeak
assert_compatible GUT.SMLWeightExpansion.totalWeak.eq_1 => Physics.SMLWeightExpansion.totalWeak.eq_1
assert_compatible GUT.SMLWeightExpansion.weakWeight => Physics.SMLWeightExpansion.weakWeight
