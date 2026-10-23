import Physics.StandardModel.Operators.Higgs.OutsideFamilyHiggsTrials
import Physics.StandardModel.Operators.ContentHiggsSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Higgs.OutsideFamilyHiggsTrials instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ContentHiggsSupport.flavor.congr_simp => Physics.ContentHiggsSupport.flavor.congr_simp,
  GUT.OutsideFamilyHiggsTrials.emptyCoefficient => Physics.OutsideFamilyHiggsTrials.emptyCoefficient,
  GUT.OutsideFamilyHiggsTrials.emptyCoefficient.eq_1 => Physics.OutsideFamilyHiggsTrials.emptyCoefficient.eq_1,
  GUT.OutsideFamilyHiggsTrials.emptyCoefficient_nonzero => Physics.OutsideFamilyHiggsTrials.emptyCoefficient_nonzero,
  GUT.OutsideFamilyHiggsTrials.emptyContent => Physics.OutsideFamilyHiggsTrials.emptyContent,
  GUT.OutsideFamilyHiggsTrials.empty_seed => Physics.OutsideFamilyHiggsTrials.empty_seed,
  GUT.OutsideFamilyHiggsTrials.neutral_arithmetic_not_sufficient => Physics.OutsideFamilyHiggsTrials.neutral_arithmetic_not_sufficient,
  GUT.OutsideFamilyHiggsTrials.scalar_only_allowed_iff => Physics.OutsideFamilyHiggsTrials.scalar_only_allowed_iff,
  GUT.OutsideFamilyHiggsTrials.sixPattern => Physics.OutsideFamilyHiggsTrials.sixPattern,
  GUT.OutsideFamilyHiggsTrials.sixPattern.eq_1 => Physics.OutsideFamilyHiggsTrials.sixPattern.eq_1,
  GUT.OutsideFamilyHiggsTrials.sixQuarks => Physics.OutsideFamilyHiggsTrials.sixQuarks,
  GUT.OutsideFamilyHiggsTrials.six_hyper => Physics.OutsideFamilyHiggsTrials.six_hyper,
  GUT.OutsideFamilyHiggsTrials.six_iff_of_seed => Physics.OutsideFamilyHiggsTrials.six_iff_of_seed,
  GUT.OutsideFamilyHiggsTrials.six_necessary => Physics.OutsideFamilyHiggsTrials.six_necessary,
  GUT.OutsideFamilyHiggsTrials.six_obstructed => Physics.OutsideFamilyHiggsTrials.six_obstructed,
  GUT.OutsideFamilyHiggsTrials.six_stable => Physics.OutsideFamilyHiggsTrials.six_stable,
  GUT.OutsideFamilyHiggsTrials.six_weight => Physics.OutsideFamilyHiggsTrials.six_weight,
  GUT.OutsideFamilyHiggsTrials.tripleQ => Physics.OutsideFamilyHiggsTrials.tripleQ,
  GUT.OutsideFamilyHiggsTrials.tripleQ_forbidden => Physics.OutsideFamilyHiggsTrials.tripleQ_forbidden,
  GUT.OutsideFamilyHiggsTrials.tripleQ_hyper => Physics.OutsideFamilyHiggsTrials.tripleQ_hyper,
  GUT.OutsideFamilyHiggsTrials.tripleQ_weight => Physics.OutsideFamilyHiggsTrials.tripleQ_weight
]

assert_compatible GUT.ContentHiggsSupport.flavor.congr_simp => Physics.ContentHiggsSupport.flavor.congr_simp
assert_compatible GUT.OutsideFamilyHiggsTrials.emptyCoefficient => Physics.OutsideFamilyHiggsTrials.emptyCoefficient
assert_compatible GUT.OutsideFamilyHiggsTrials.emptyCoefficient.eq_1 => Physics.OutsideFamilyHiggsTrials.emptyCoefficient.eq_1
assert_compatible GUT.OutsideFamilyHiggsTrials.emptyCoefficient_nonzero => Physics.OutsideFamilyHiggsTrials.emptyCoefficient_nonzero
assert_compatible GUT.OutsideFamilyHiggsTrials.emptyContent => Physics.OutsideFamilyHiggsTrials.emptyContent
assert_compatible GUT.OutsideFamilyHiggsTrials.empty_seed => Physics.OutsideFamilyHiggsTrials.empty_seed
assert_compatible GUT.OutsideFamilyHiggsTrials.neutral_arithmetic_not_sufficient => Physics.OutsideFamilyHiggsTrials.neutral_arithmetic_not_sufficient
assert_compatible GUT.OutsideFamilyHiggsTrials.scalar_only_allowed_iff => Physics.OutsideFamilyHiggsTrials.scalar_only_allowed_iff
assert_compatible GUT.OutsideFamilyHiggsTrials.sixPattern => Physics.OutsideFamilyHiggsTrials.sixPattern
assert_compatible GUT.OutsideFamilyHiggsTrials.sixPattern.eq_1 => Physics.OutsideFamilyHiggsTrials.sixPattern.eq_1
assert_compatible GUT.OutsideFamilyHiggsTrials.sixQuarks => Physics.OutsideFamilyHiggsTrials.sixQuarks
assert_compatible GUT.OutsideFamilyHiggsTrials.six_hyper => Physics.OutsideFamilyHiggsTrials.six_hyper
assert_compatible GUT.OutsideFamilyHiggsTrials.six_iff_of_seed => Physics.OutsideFamilyHiggsTrials.six_iff_of_seed
assert_compatible GUT.OutsideFamilyHiggsTrials.six_necessary => Physics.OutsideFamilyHiggsTrials.six_necessary
assert_compatible GUT.OutsideFamilyHiggsTrials.six_obstructed => Physics.OutsideFamilyHiggsTrials.six_obstructed
assert_compatible GUT.OutsideFamilyHiggsTrials.six_stable => Physics.OutsideFamilyHiggsTrials.six_stable
assert_compatible GUT.OutsideFamilyHiggsTrials.six_weight => Physics.OutsideFamilyHiggsTrials.six_weight
assert_compatible GUT.OutsideFamilyHiggsTrials.tripleQ => Physics.OutsideFamilyHiggsTrials.tripleQ
assert_compatible GUT.OutsideFamilyHiggsTrials.tripleQ_forbidden => Physics.OutsideFamilyHiggsTrials.tripleQ_forbidden
assert_compatible GUT.OutsideFamilyHiggsTrials.tripleQ_hyper => Physics.OutsideFamilyHiggsTrials.tripleQ_hyper
assert_compatible GUT.OutsideFamilyHiggsTrials.tripleQ_weight => Physics.OutsideFamilyHiggsTrials.tripleQ_weight
