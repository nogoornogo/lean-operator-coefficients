import Physics.StandardModel.Operators.Higgs.ContentHiggsSupport
import Physics.StandardModel.Operators.FourFamilyHiggsContent
import Physics.StandardModel.Operators.AdmittedCyclicSMProhibition
import Physics.StandardModel.Operators.ThreeGenerationFermionBound
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Higgs.ContentHiggsSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ContentHiggsSupport.SeedSpace => Physics.ContentHiggsSupport.SeedSpace,
  GUT.ContentHiggsSupport.Space => Physics.ContentHiggsSupport.Space,
  GUT.ContentHiggsSupport.above_bound_forbidden => Physics.ContentHiggsSupport.above_bound_forbidden,
  GUT.ContentHiggsSupport.all_forbidden_iff => Physics.ContentHiggsSupport.all_forbidden_iff,
  GUT.ContentHiggsSupport.allowed_iff => Physics.ContentHiggsSupport.allowed_iff,
  GUT.ContentHiggsSupport.charge => Physics.ContentHiggsSupport.charge,
  GUT.ContentHiggsSupport.charge_of_nonzero => Physics.ContentHiggsSupport.charge_of_nonzero,
  GUT.ContentHiggsSupport.dress => Physics.ContentHiggsSupport.dress,
  GUT.ContentHiggsSupport.dress_nonzero => Physics.ContentHiggsSupport.dress_nonzero,
  GUT.ContentHiggsSupport.exists_value => Physics.ContentHiggsSupport.exists_value,
  GUT.ContentHiggsSupport.family => Physics.ContentHiggsSupport.family,
  GUT.ContentHiggsSupport.family.eq_1 => Physics.ContentHiggsSupport.family.eq_1,
  GUT.ContentHiggsSupport.family_allowed_iff => Physics.ContentHiggsSupport.family_allowed_iff,
  GUT.ContentHiggsSupport.family_control => Physics.ContentHiggsSupport.family_control,
  GUT.ContentHiggsSupport.family_hyper => Physics.ContentHiggsSupport.family_hyper,
  GUT.ContentHiggsSupport.family_seed => Physics.ContentHiggsSupport.family_seed,
  GUT.ContentHiggsSupport.family_stable => Physics.ContentHiggsSupport.family_stable,
  GUT.ContentHiggsSupport.family_weight => Physics.ContentHiggsSupport.family_weight,
  GUT.ContentHiggsSupport.flavor => Physics.ContentHiggsSupport.flavor,
  GUT.ContentHiggsSupport.forbidden_iff => Physics.ContentHiggsSupport.forbidden_iff,
  GUT.ContentHiggsSupport.hypercharge_divisible => Physics.ContentHiggsSupport.hypercharge_divisible,
  GUT.ContentHiggsSupport.hypercharge_of_nonzero => Physics.ContentHiggsSupport.hypercharge_of_nonzero,
  GUT.ContentHiggsSupport.indivisible_forbidden => Physics.ContentHiggsSupport.indivisible_forbidden,
  GUT.ContentHiggsSupport.leptonPair => Physics.ContentHiggsSupport.leptonPair,
  GUT.ContentHiggsSupport.leptonPair_balanced_forbidden => Physics.ContentHiggsSupport.leptonPair_balanced_forbidden,
  GUT.ContentHiggsSupport.leptonPair_hyper => Physics.ContentHiggsSupport.leptonPair_hyper,
  GUT.ContentHiggsSupport.leptonPair_necessary => Physics.ContentHiggsSupport.leptonPair_necessary,
  GUT.ContentHiggsSupport.leptonPair_weight => Physics.ContentHiggsSupport.leptonPair_weight,
  GUT.ContentHiggsSupport.necessary => Physics.ContentHiggsSupport.necessary,
  GUT.ContentHiggsSupport.obstructed => Physics.ContentHiggsSupport.obstructed,
  GUT.ContentHiggsSupport.odd_forbidden => Physics.ContentHiggsSupport.odd_forbidden,
  GUT.ContentHiggsSupport.rawDress => Physics.ContentHiggsSupport.rawDress,
  GUT.ContentHiggsSupport.rawDress_mem => Physics.ContentHiggsSupport.rawDress_mem,
  GUT.ContentHiggsSupport.scalar => Physics.ContentHiggsSupport.scalar,
  GUT.ContentHiggsSupport.selected => Physics.ContentHiggsSupport.selected,
  GUT.ContentHiggsSupport.selected.eq_1 => Physics.ContentHiggsSupport.selected.eq_1,
  GUT.ContentHiggsSupport.selected_stable => Physics.ContentHiggsSupport.selected_stable
]

assert_compatible GUT.ContentHiggsSupport.SeedSpace => Physics.ContentHiggsSupport.SeedSpace
assert_compatible GUT.ContentHiggsSupport.Space => Physics.ContentHiggsSupport.Space
assert_compatible GUT.ContentHiggsSupport.above_bound_forbidden => Physics.ContentHiggsSupport.above_bound_forbidden
assert_compatible GUT.ContentHiggsSupport.all_forbidden_iff => Physics.ContentHiggsSupport.all_forbidden_iff
assert_compatible GUT.ContentHiggsSupport.allowed_iff => Physics.ContentHiggsSupport.allowed_iff
assert_compatible GUT.ContentHiggsSupport.charge => Physics.ContentHiggsSupport.charge
assert_compatible GUT.ContentHiggsSupport.charge_of_nonzero => Physics.ContentHiggsSupport.charge_of_nonzero
assert_compatible GUT.ContentHiggsSupport.dress => Physics.ContentHiggsSupport.dress
assert_compatible GUT.ContentHiggsSupport.dress_nonzero => Physics.ContentHiggsSupport.dress_nonzero
assert_compatible GUT.ContentHiggsSupport.exists_value => Physics.ContentHiggsSupport.exists_value
assert_compatible GUT.ContentHiggsSupport.family => Physics.ContentHiggsSupport.family
assert_compatible GUT.ContentHiggsSupport.family.eq_1 => Physics.ContentHiggsSupport.family.eq_1
assert_compatible GUT.ContentHiggsSupport.family_allowed_iff => Physics.ContentHiggsSupport.family_allowed_iff
assert_compatible GUT.ContentHiggsSupport.family_control => Physics.ContentHiggsSupport.family_control
assert_compatible GUT.ContentHiggsSupport.family_hyper => Physics.ContentHiggsSupport.family_hyper
assert_compatible GUT.ContentHiggsSupport.family_seed => Physics.ContentHiggsSupport.family_seed
assert_compatible GUT.ContentHiggsSupport.family_stable => Physics.ContentHiggsSupport.family_stable
assert_compatible GUT.ContentHiggsSupport.family_weight => Physics.ContentHiggsSupport.family_weight
assert_compatible GUT.ContentHiggsSupport.flavor => Physics.ContentHiggsSupport.flavor
assert_compatible GUT.ContentHiggsSupport.forbidden_iff => Physics.ContentHiggsSupport.forbidden_iff
assert_compatible GUT.ContentHiggsSupport.hypercharge_divisible => Physics.ContentHiggsSupport.hypercharge_divisible
assert_compatible GUT.ContentHiggsSupport.hypercharge_of_nonzero => Physics.ContentHiggsSupport.hypercharge_of_nonzero
assert_compatible GUT.ContentHiggsSupport.indivisible_forbidden => Physics.ContentHiggsSupport.indivisible_forbidden
assert_compatible GUT.ContentHiggsSupport.leptonPair => Physics.ContentHiggsSupport.leptonPair
assert_compatible GUT.ContentHiggsSupport.leptonPair_balanced_forbidden => Physics.ContentHiggsSupport.leptonPair_balanced_forbidden
assert_compatible GUT.ContentHiggsSupport.leptonPair_hyper => Physics.ContentHiggsSupport.leptonPair_hyper
assert_compatible GUT.ContentHiggsSupport.leptonPair_necessary => Physics.ContentHiggsSupport.leptonPair_necessary
assert_compatible GUT.ContentHiggsSupport.leptonPair_weight => Physics.ContentHiggsSupport.leptonPair_weight
assert_compatible GUT.ContentHiggsSupport.necessary => Physics.ContentHiggsSupport.necessary
assert_compatible GUT.ContentHiggsSupport.obstructed => Physics.ContentHiggsSupport.obstructed
assert_compatible GUT.ContentHiggsSupport.odd_forbidden => Physics.ContentHiggsSupport.odd_forbidden
assert_compatible GUT.ContentHiggsSupport.rawDress => Physics.ContentHiggsSupport.rawDress
assert_compatible GUT.ContentHiggsSupport.rawDress_mem => Physics.ContentHiggsSupport.rawDress_mem
assert_compatible GUT.ContentHiggsSupport.scalar => Physics.ContentHiggsSupport.scalar
assert_compatible GUT.ContentHiggsSupport.selected => Physics.ContentHiggsSupport.selected
assert_compatible GUT.ContentHiggsSupport.selected.eq_1 => Physics.ContentHiggsSupport.selected.eq_1
assert_compatible GUT.ContentHiggsSupport.selected_stable => Physics.ContentHiggsSupport.selected_stable
