import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteHiggsSupport
import Physics.StandardModel.Operators.SMContentWeakBound
import Physics.StandardModel.Operators.FullHiggsCoefficientBridge
import Math.RepresentationTheory.BoundedHiggsSupport
import Math.RepresentationTheory.PatternCoefficientSupport
import Math.RepresentationTheory.InvariantTensorCharge
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMFiniteHiggsSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMFiniteHiggsSupport.FullSource => Physics.SMFiniteHiggsSupport.FullSource,
  GUT.SMFiniteHiggsSupport.OriginalSpace => Physics.SMFiniteHiggsSupport.OriginalSpace,
  GUT.SMFiniteHiggsSupport.Scalars => Physics.SMFiniteHiggsSupport.Scalars,
  GUT.SMFiniteHiggsSupport.Space => Physics.SMFiniteHiggsSupport.Space,
  GUT.SMFiniteHiggsSupport.Test => Physics.SMFiniteHiggsSupport.Test,
  GUT.SMFiniteHiggsSupport.constituent_hypercharge => Physics.SMFiniteHiggsSupport.constituent_hypercharge,
  GUT.SMFiniteHiggsSupport.finite_allowed_iff => Physics.SMFiniteHiggsSupport.finite_allowed_iff,
  GUT.SMFiniteHiggsSupport.mem_original_iff => Physics.SMFiniteHiggsSupport.mem_original_iff,
  GUT.SMFiniteHiggsSupport.originalEquiv => Physics.SMFiniteHiggsSupport.originalEquiv,
  GUT.SMFiniteHiggsSupport.original_allowed_iff => Physics.SMFiniteHiggsSupport.original_allowed_iff,
  GUT.SMFiniteHiggsSupport.original_charge_finite_iff => Physics.SMFiniteHiggsSupport.original_charge_finite_iff,
  GUT.SMFiniteHiggsSupport.original_degree_forbidden => Physics.SMFiniteHiggsSupport.original_degree_forbidden,
  GUT.SMFiniteHiggsSupport.original_forbidden_iff => Physics.SMFiniteHiggsSupport.original_forbidden_iff,
  GUT.SMFiniteHiggsSupport.original_imbalance_forbidden => Physics.SMFiniteHiggsSupport.original_imbalance_forbidden,
  GUT.SMFiniteHiggsSupport.original_pair_monotone => Physics.SMFiniteHiggsSupport.original_pair_monotone,
  GUT.SMFiniteHiggsSupport.original_pair_stable => Physics.SMFiniteHiggsSupport.original_pair_stable,
  GUT.SMFiniteHiggsSupport.original_pairs_stable => Physics.SMFiniteHiggsSupport.original_pairs_stable,
  GUT.SMFiniteHiggsSupport.original_table_iff => Physics.SMFiniteHiggsSupport.original_table_iff,
  GUT.SMFiniteHiggsSupport.source => Physics.SMFiniteHiggsSupport.source,
  GUT.SMFiniteHiggsSupport.source_bound => Physics.SMFiniteHiggsSupport.source_bound,
  GUT.SMFiniteHiggsSupport.split_allowed => Physics.SMFiniteHiggsSupport.split_allowed,
  GUT.SMFiniteHiggsSupport.test_charge => Physics.SMFiniteHiggsSupport.test_charge,
  GUT.SMFiniteHiggsSupport.weak_character => Physics.SMFiniteHiggsSupport.weak_character,
  GUT.SMFiniteHiggsSupport.weak_projection => Physics.SMFiniteHiggsSupport.weak_projection
]

assert_compatible GUT.SMFiniteHiggsSupport.FullSource => Physics.SMFiniteHiggsSupport.FullSource
assert_compatible GUT.SMFiniteHiggsSupport.OriginalSpace => Physics.SMFiniteHiggsSupport.OriginalSpace
assert_compatible GUT.SMFiniteHiggsSupport.Scalars => Physics.SMFiniteHiggsSupport.Scalars
assert_compatible GUT.SMFiniteHiggsSupport.Space => Physics.SMFiniteHiggsSupport.Space
assert_compatible GUT.SMFiniteHiggsSupport.Test => Physics.SMFiniteHiggsSupport.Test
assert_compatible GUT.SMFiniteHiggsSupport.constituent_hypercharge => Physics.SMFiniteHiggsSupport.constituent_hypercharge
assert_compatible GUT.SMFiniteHiggsSupport.finite_allowed_iff => Physics.SMFiniteHiggsSupport.finite_allowed_iff
assert_compatible GUT.SMFiniteHiggsSupport.mem_original_iff => Physics.SMFiniteHiggsSupport.mem_original_iff
assert_compatible GUT.SMFiniteHiggsSupport.originalEquiv => Physics.SMFiniteHiggsSupport.originalEquiv
assert_compatible GUT.SMFiniteHiggsSupport.original_allowed_iff => Physics.SMFiniteHiggsSupport.original_allowed_iff
assert_compatible GUT.SMFiniteHiggsSupport.original_charge_finite_iff => Physics.SMFiniteHiggsSupport.original_charge_finite_iff
assert_compatible GUT.SMFiniteHiggsSupport.original_degree_forbidden => Physics.SMFiniteHiggsSupport.original_degree_forbidden
assert_compatible GUT.SMFiniteHiggsSupport.original_forbidden_iff => Physics.SMFiniteHiggsSupport.original_forbidden_iff
assert_compatible GUT.SMFiniteHiggsSupport.original_imbalance_forbidden => Physics.SMFiniteHiggsSupport.original_imbalance_forbidden
assert_compatible GUT.SMFiniteHiggsSupport.original_pair_monotone => Physics.SMFiniteHiggsSupport.original_pair_monotone
assert_compatible GUT.SMFiniteHiggsSupport.original_pair_stable => Physics.SMFiniteHiggsSupport.original_pair_stable
assert_compatible GUT.SMFiniteHiggsSupport.original_pairs_stable => Physics.SMFiniteHiggsSupport.original_pairs_stable
assert_compatible GUT.SMFiniteHiggsSupport.original_table_iff => Physics.SMFiniteHiggsSupport.original_table_iff
assert_compatible GUT.SMFiniteHiggsSupport.source => Physics.SMFiniteHiggsSupport.source
assert_compatible GUT.SMFiniteHiggsSupport.source_bound => Physics.SMFiniteHiggsSupport.source_bound
assert_compatible GUT.SMFiniteHiggsSupport.split_allowed => Physics.SMFiniteHiggsSupport.split_allowed
assert_compatible GUT.SMFiniteHiggsSupport.test_charge => Physics.SMFiniteHiggsSupport.test_charge
assert_compatible GUT.SMFiniteHiggsSupport.weak_character => Physics.SMFiniteHiggsSupport.weak_character
assert_compatible GUT.SMFiniteHiggsSupport.weak_projection => Physics.SMFiniteHiggsSupport.weak_projection
