import Physics.StandardModel.Operators.Higgs.WeakSingletHiggsSupport
import Math.RepresentationTheory.WeakSingletHiggsReduction
import Physics.StandardModel.Operators.NeutralHiggsPowers
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Higgs.WeakSingletHiggsSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeakSingletHiggsSupport.Space => Physics.WeakSingletHiggsSupport.Space,
  GUT.WeakSingletHiggsSupport.all_forbidden_iff => Physics.WeakSingletHiggsSupport.all_forbidden_iff,
  GUT.WeakSingletHiggsSupport.all_matter_forbidden_zero_iff => Physics.WeakSingletHiggsSupport.all_matter_forbidden_zero_iff,
  GUT.WeakSingletHiggsSupport.allowed_iff => Physics.WeakSingletHiggsSupport.allowed_iff,
  GUT.WeakSingletHiggsSupport.equiv => Physics.WeakSingletHiggsSupport.equiv,
  GUT.WeakSingletHiggsSupport.exterior_weak => Physics.WeakSingletHiggsSupport.exterior_weak,
  GUT.WeakSingletHiggsSupport.forbidden_iff => Physics.WeakSingletHiggsSupport.forbidden_iff,
  GUT.WeakSingletHiggsSupport.higgs_weak => Physics.WeakSingletHiggsSupport.higgs_weak,
  GUT.WeakSingletHiggsSupport.matter => Physics.WeakSingletHiggsSupport.matter,
  GUT.WeakSingletHiggsSupport.matterEquiv => Physics.WeakSingletHiggsSupport.matterEquiv,
  GUT.WeakSingletHiggsSupport.matterZeroDegreeReduction => Physics.WeakSingletHiggsSupport.matterZeroDegreeReduction,
  GUT.WeakSingletHiggsSupport.matter_allowed_iff => Physics.WeakSingletHiggsSupport.matter_allowed_iff,
  GUT.WeakSingletHiggsSupport.matter_weak => Physics.WeakSingletHiggsSupport.matter_weak,
  GUT.WeakSingletHiggsSupport.scalarEquiv => Physics.WeakSingletHiggsSupport.scalarEquiv,
  GUT.WeakSingletHiggsSupport.singletSpecies => Physics.WeakSingletHiggsSupport.singletSpecies,
  GUT.WeakSingletHiggsSupport.singlet_field_weak => Physics.WeakSingletHiggsSupport.singlet_field_weak,
  GUT.WeakSingletHiggsSupport.singlet_gauge_weak => Physics.WeakSingletHiggsSupport.singlet_gauge_weak,
  GUT.WeakSingletHiggsSupport.weakInclusion => Physics.WeakSingletHiggsSupport.weakInclusion
]

assert_compatible GUT.WeakSingletHiggsSupport.Space => Physics.WeakSingletHiggsSupport.Space
assert_compatible GUT.WeakSingletHiggsSupport.all_forbidden_iff => Physics.WeakSingletHiggsSupport.all_forbidden_iff
assert_compatible GUT.WeakSingletHiggsSupport.all_matter_forbidden_zero_iff => Physics.WeakSingletHiggsSupport.all_matter_forbidden_zero_iff
assert_compatible GUT.WeakSingletHiggsSupport.allowed_iff => Physics.WeakSingletHiggsSupport.allowed_iff
assert_compatible GUT.WeakSingletHiggsSupport.equiv => Physics.WeakSingletHiggsSupport.equiv
assert_compatible GUT.WeakSingletHiggsSupport.exterior_weak => Physics.WeakSingletHiggsSupport.exterior_weak
assert_compatible GUT.WeakSingletHiggsSupport.forbidden_iff => Physics.WeakSingletHiggsSupport.forbidden_iff
assert_compatible GUT.WeakSingletHiggsSupport.higgs_weak => Physics.WeakSingletHiggsSupport.higgs_weak
assert_compatible GUT.WeakSingletHiggsSupport.matter => Physics.WeakSingletHiggsSupport.matter
assert_compatible GUT.WeakSingletHiggsSupport.matterEquiv => Physics.WeakSingletHiggsSupport.matterEquiv
assert_compatible GUT.WeakSingletHiggsSupport.matterZeroDegreeReduction => Physics.WeakSingletHiggsSupport.matterZeroDegreeReduction
assert_compatible GUT.WeakSingletHiggsSupport.matter_allowed_iff => Physics.WeakSingletHiggsSupport.matter_allowed_iff
assert_compatible GUT.WeakSingletHiggsSupport.matter_weak => Physics.WeakSingletHiggsSupport.matter_weak
assert_compatible GUT.WeakSingletHiggsSupport.scalarEquiv => Physics.WeakSingletHiggsSupport.scalarEquiv
assert_compatible GUT.WeakSingletHiggsSupport.singletSpecies => Physics.WeakSingletHiggsSupport.singletSpecies
assert_compatible GUT.WeakSingletHiggsSupport.singlet_field_weak => Physics.WeakSingletHiggsSupport.singlet_field_weak
assert_compatible GUT.WeakSingletHiggsSupport.singlet_gauge_weak => Physics.WeakSingletHiggsSupport.singlet_gauge_weak
assert_compatible GUT.WeakSingletHiggsSupport.weakInclusion => Physics.WeakSingletHiggsSupport.weakInclusion
