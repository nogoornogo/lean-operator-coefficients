import Physics.StandardModel.Operators.Selection.InverseCyclicSMCharges
import Physics.StandardModel.Operators.CyclicResidualSelection
import Physics.StandardModel.Operators.FlavoredCyclicSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.InverseCyclicSMCharges instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InverseCyclicSMCharges.YukawaNeutral => Physics.InverseCyclicSMCharges.YukawaNeutral,
  GUT.InverseCyclicSMCharges.YukawaNeutral.eq_1 => Physics.InverseCyclicSMCharges.YukawaNeutral.eq_1,
  GUT.InverseCyclicSMCharges.all_family_charges => Physics.InverseCyclicSMCharges.all_family_charges,
  GUT.InverseCyclicSMCharges.bounded_four_forbidden_iff => Physics.InverseCyclicSMCharges.bounded_four_forbidden_iff,
  GUT.InverseCyclicSMCharges.candidate_iff_three_generation_forbidden => Physics.InverseCyclicSMCharges.candidate_iff_three_generation_forbidden,
  GUT.InverseCyclicSMCharges.candidates => Physics.InverseCyclicSMCharges.candidates,
  GUT.InverseCyclicSMCharges.candidates.eq_1 => Physics.InverseCyclicSMCharges.candidates.eq_1,
  GUT.InverseCyclicSMCharges.chiral => Physics.InverseCyclicSMCharges.chiral,
  GUT.InverseCyclicSMCharges.chiral.eq_1 => Physics.InverseCyclicSMCharges.chiral.eq_1,
  GUT.InverseCyclicSMCharges.counts => Physics.InverseCyclicSMCharges.counts,
  GUT.InverseCyclicSMCharges.initial_count => Physics.InverseCyclicSMCharges.initial_count,
  GUT.InverseCyclicSMCharges.mem_candidates => Physics.InverseCyclicSMCharges.mem_candidates,
  GUT.InverseCyclicSMCharges.not_candidate_iff_three_generation_allowed => Physics.InverseCyclicSMCharges.not_candidate_iff_three_generation_allowed,
  GUT.InverseCyclicSMCharges.physical => Physics.InverseCyclicSMCharges.physical,
  GUT.InverseCyclicSMCharges.physical.eq_1 => Physics.InverseCyclicSMCharges.physical.eq_1,
  GUT.InverseCyclicSMCharges.physical_dictionary => Physics.InverseCyclicSMCharges.physical_dictionary,
  GUT.InverseCyclicSMCharges.selected_candidate => Physics.InverseCyclicSMCharges.selected_candidate,
  GUT.InverseCyclicSMCharges.selected_least => Physics.InverseCyclicSMCharges.selected_least,
  GUT.InverseCyclicSMCharges.surviving_count => Physics.InverseCyclicSMCharges.surviving_count,
  GUT.InverseCyclicSMCharges.three_generation_allowed_iff => Physics.InverseCyclicSMCharges.three_generation_allowed_iff,
  GUT.InverseCyclicSMCharges.three_generation_forbidden_iff => Physics.InverseCyclicSMCharges.three_generation_forbidden_iff,
  GUT.InverseCyclicSMCharges.three_generation_necessary => Physics.InverseCyclicSMCharges.three_generation_necessary,
  GUT.InverseCyclicSMCharges.three_generation_sufficient => Physics.InverseCyclicSMCharges.three_generation_sufficient,
  GUT.InverseCyclicSMCharges.universal => Physics.InverseCyclicSMCharges.universal,
  GUT.InverseCyclicSMCharges.universal.eq_1 => Physics.InverseCyclicSMCharges.universal.eq_1,
  GUT.InverseCyclicSMCharges.universal_qqql_charge => Physics.InverseCyclicSMCharges.universal_qqql_charge,
  GUT.InverseCyclicSMCharges.universal_qque_charge => Physics.InverseCyclicSMCharges.universal_qque_charge,
  GUT.InverseCyclicSMCharges.yukawa_parametrization => Physics.InverseCyclicSMCharges.yukawa_parametrization
]

assert_compatible GUT.InverseCyclicSMCharges.YukawaNeutral => Physics.InverseCyclicSMCharges.YukawaNeutral
assert_compatible GUT.InverseCyclicSMCharges.YukawaNeutral.eq_1 => Physics.InverseCyclicSMCharges.YukawaNeutral.eq_1
assert_compatible GUT.InverseCyclicSMCharges.all_family_charges => Physics.InverseCyclicSMCharges.all_family_charges
assert_compatible GUT.InverseCyclicSMCharges.bounded_four_forbidden_iff => Physics.InverseCyclicSMCharges.bounded_four_forbidden_iff
assert_compatible GUT.InverseCyclicSMCharges.candidate_iff_three_generation_forbidden => Physics.InverseCyclicSMCharges.candidate_iff_three_generation_forbidden
assert_compatible GUT.InverseCyclicSMCharges.candidates => Physics.InverseCyclicSMCharges.candidates
assert_compatible GUT.InverseCyclicSMCharges.candidates.eq_1 => Physics.InverseCyclicSMCharges.candidates.eq_1
assert_compatible GUT.InverseCyclicSMCharges.chiral => Physics.InverseCyclicSMCharges.chiral
assert_compatible GUT.InverseCyclicSMCharges.chiral.eq_1 => Physics.InverseCyclicSMCharges.chiral.eq_1
assert_compatible GUT.InverseCyclicSMCharges.counts => Physics.InverseCyclicSMCharges.counts
assert_compatible GUT.InverseCyclicSMCharges.initial_count => Physics.InverseCyclicSMCharges.initial_count
assert_compatible GUT.InverseCyclicSMCharges.mem_candidates => Physics.InverseCyclicSMCharges.mem_candidates
assert_compatible GUT.InverseCyclicSMCharges.not_candidate_iff_three_generation_allowed => Physics.InverseCyclicSMCharges.not_candidate_iff_three_generation_allowed
assert_compatible GUT.InverseCyclicSMCharges.physical => Physics.InverseCyclicSMCharges.physical
assert_compatible GUT.InverseCyclicSMCharges.physical.eq_1 => Physics.InverseCyclicSMCharges.physical.eq_1
assert_compatible GUT.InverseCyclicSMCharges.physical_dictionary => Physics.InverseCyclicSMCharges.physical_dictionary
assert_compatible GUT.InverseCyclicSMCharges.selected_candidate => Physics.InverseCyclicSMCharges.selected_candidate
assert_compatible GUT.InverseCyclicSMCharges.selected_least => Physics.InverseCyclicSMCharges.selected_least
assert_compatible GUT.InverseCyclicSMCharges.surviving_count => Physics.InverseCyclicSMCharges.surviving_count
assert_compatible GUT.InverseCyclicSMCharges.three_generation_allowed_iff => Physics.InverseCyclicSMCharges.three_generation_allowed_iff
assert_compatible GUT.InverseCyclicSMCharges.three_generation_forbidden_iff => Physics.InverseCyclicSMCharges.three_generation_forbidden_iff
assert_compatible GUT.InverseCyclicSMCharges.three_generation_necessary => Physics.InverseCyclicSMCharges.three_generation_necessary
assert_compatible GUT.InverseCyclicSMCharges.three_generation_sufficient => Physics.InverseCyclicSMCharges.three_generation_sufficient
assert_compatible GUT.InverseCyclicSMCharges.universal => Physics.InverseCyclicSMCharges.universal
assert_compatible GUT.InverseCyclicSMCharges.universal.eq_1 => Physics.InverseCyclicSMCharges.universal.eq_1
assert_compatible GUT.InverseCyclicSMCharges.universal_qqql_charge => Physics.InverseCyclicSMCharges.universal_qqql_charge
assert_compatible GUT.InverseCyclicSMCharges.universal_qque_charge => Physics.InverseCyclicSMCharges.universal_qque_charge
assert_compatible GUT.InverseCyclicSMCharges.yukawa_parametrization => Physics.InverseCyclicSMCharges.yukawa_parametrization
