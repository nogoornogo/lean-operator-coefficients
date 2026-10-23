import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveSum
import Physics.FieldTheory.Jets.WeylHiggsWaveValues
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Basic
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveSum instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsWaveSum.annihilates => Physics.WeylHiggsWaveSum.annihilates,
  GUT.WeylHiggsWaveSum.bySpin => Physics.WeylHiggsWaveSum.bySpin,
  GUT.WeylHiggsWaveSum.bySpin.eq_1 => Physics.WeylHiggsWaveSum.bySpin.eq_1,
  GUT.WeylHiggsWaveSum.bySpin_annihilates => Physics.WeylHiggsWaveSum.bySpin_annihilates,
  GUT.WeylHiggsWaveSum.bySpin_candidate => Physics.WeylHiggsWaveSum.bySpin_candidate,
  GUT.WeylHiggsWaveSum.candidate_value => Physics.WeylHiggsWaveSum.candidate_value,
  GUT.WeylHiggsWaveSum.color_sum => Physics.WeylHiggsWaveSum.color_sum,
  GUT.WeylHiggsWaveSum.functional => Physics.WeylHiggsWaveSum.functional,
  GUT.WeylHiggsWaveSum.functional.eq_1 => Physics.WeylHiggsWaveSum.functional.eq_1,
  GUT.WeylHiggsWaveSum.moment => Physics.WeylHiggsWaveSum.moment,
  GUT.WeylHiggsWaveSum.momentum => Physics.WeylHiggsWaveSum.momentum,
  GUT.WeylHiggsWaveSum.momentum.eq_1 => Physics.WeylHiggsWaveSum.momentum.eq_1,
  GUT.WeylHiggsWaveSum.null => Physics.WeylHiggsWaveSum.null,
  GUT.WeylHiggsWaveSum.spin_moment => Physics.WeylHiggsWaveSum.spin_moment,
  GUT.WeylHiggsWaveSum.weight => Physics.WeylHiggsWaveSum.weight,
  GUT.WeylHiggsWaveSum.weight.eq_1 => Physics.WeylHiggsWaveSum.weight.eq_1
]

assert_compatible GUT.WeylHiggsWaveSum.annihilates => Physics.WeylHiggsWaveSum.annihilates
assert_compatible GUT.WeylHiggsWaveSum.bySpin => Physics.WeylHiggsWaveSum.bySpin
assert_compatible GUT.WeylHiggsWaveSum.bySpin.eq_1 => Physics.WeylHiggsWaveSum.bySpin.eq_1
assert_compatible GUT.WeylHiggsWaveSum.bySpin_annihilates => Physics.WeylHiggsWaveSum.bySpin_annihilates
assert_compatible GUT.WeylHiggsWaveSum.bySpin_candidate => Physics.WeylHiggsWaveSum.bySpin_candidate
assert_compatible GUT.WeylHiggsWaveSum.candidate_value => Physics.WeylHiggsWaveSum.candidate_value
assert_compatible GUT.WeylHiggsWaveSum.color_sum => Physics.WeylHiggsWaveSum.color_sum
assert_compatible GUT.WeylHiggsWaveSum.functional => Physics.WeylHiggsWaveSum.functional
assert_compatible GUT.WeylHiggsWaveSum.functional.eq_1 => Physics.WeylHiggsWaveSum.functional.eq_1
assert_compatible GUT.WeylHiggsWaveSum.moment => Physics.WeylHiggsWaveSum.moment
assert_compatible GUT.WeylHiggsWaveSum.momentum => Physics.WeylHiggsWaveSum.momentum
assert_compatible GUT.WeylHiggsWaveSum.momentum.eq_1 => Physics.WeylHiggsWaveSum.momentum.eq_1
assert_compatible GUT.WeylHiggsWaveSum.null => Physics.WeylHiggsWaveSum.null
assert_compatible GUT.WeylHiggsWaveSum.spin_moment => Physics.WeylHiggsWaveSum.spin_moment
assert_compatible GUT.WeylHiggsWaveSum.weight => Physics.WeylHiggsWaveSum.weight
assert_compatible GUT.WeylHiggsWaveSum.weight.eq_1 => Physics.WeylHiggsWaveSum.weight.eq_1
