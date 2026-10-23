import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvMixedWeylSupport
import Physics.StandardModel.Operators.BnvMixedInput
import Physics.StandardModel.Operators.BnvBoundedSpecies
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvMixedWeylSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvMixedInput.scalarHypercharge.eq_1 => Physics.BnvMixedInput.scalarHypercharge.eq_1,
  GUT.BnvMixedWeylSupport.admissible_of_nonzero => Physics.BnvMixedWeylSupport.admissible_of_nonzero,
  GUT.BnvMixedWeylSupport.counts_dimension => Physics.BnvMixedWeylSupport.counts_dimension,
  GUT.BnvMixedWeylSupport.counts_hypercharge => Physics.BnvMixedWeylSupport.counts_hypercharge,
  GUT.BnvMixedWeylSupport.left_even_of_nonzero => Physics.BnvMixedWeylSupport.left_even_of_nonzero,
  GUT.BnvMixedWeylSupport.mixedCounts => Physics.BnvMixedWeylSupport.mixedCounts,
  GUT.BnvMixedWeylSupport.mixedCounts.eq_1 => Physics.BnvMixedWeylSupport.mixedCounts.eq_1,
  GUT.BnvMixedWeylSupport.odd_basis_vanish => Physics.BnvMixedWeylSupport.odd_basis_vanish,
  GUT.BnvMixedWeylSupport.odd_vanish => Physics.BnvMixedWeylSupport.odd_vanish,
  GUT.BnvMixedWeylSupport.scalarCount => Physics.BnvMixedWeylSupport.scalarCount,
  GUT.BnvMixedWeylSupport.scalarCount.eq_1 => Physics.BnvMixedWeylSupport.scalarCount.eq_1,
  GUT.BnvMixedWeylSupport.scalarField_spinTest => Physics.BnvMixedWeylSupport.scalarField_spinTest,
  GUT.BnvMixedWeylSupport.scalar_count_sum => Physics.BnvMixedWeylSupport.scalar_count_sum,
  GUT.BnvMixedWeylSupport.scalar_sum_weights => Physics.BnvMixedWeylSupport.scalar_sum_weights,
  GUT.BnvMixedWeylSupport.seven_support_of_nonzero => Physics.BnvMixedWeylSupport.seven_support_of_nonzero
]

assert_compatible GUT.BnvMixedInput.scalarHypercharge.eq_1 => Physics.BnvMixedInput.scalarHypercharge.eq_1
assert_compatible GUT.BnvMixedWeylSupport.admissible_of_nonzero => Physics.BnvMixedWeylSupport.admissible_of_nonzero
assert_compatible GUT.BnvMixedWeylSupport.counts_dimension => Physics.BnvMixedWeylSupport.counts_dimension
assert_compatible GUT.BnvMixedWeylSupport.counts_hypercharge => Physics.BnvMixedWeylSupport.counts_hypercharge
assert_compatible GUT.BnvMixedWeylSupport.left_even_of_nonzero => Physics.BnvMixedWeylSupport.left_even_of_nonzero
assert_compatible GUT.BnvMixedWeylSupport.mixedCounts => Physics.BnvMixedWeylSupport.mixedCounts
assert_compatible GUT.BnvMixedWeylSupport.mixedCounts.eq_1 => Physics.BnvMixedWeylSupport.mixedCounts.eq_1
assert_compatible GUT.BnvMixedWeylSupport.odd_basis_vanish => Physics.BnvMixedWeylSupport.odd_basis_vanish
assert_compatible GUT.BnvMixedWeylSupport.odd_vanish => Physics.BnvMixedWeylSupport.odd_vanish
assert_compatible GUT.BnvMixedWeylSupport.scalarCount => Physics.BnvMixedWeylSupport.scalarCount
assert_compatible GUT.BnvMixedWeylSupport.scalarCount.eq_1 => Physics.BnvMixedWeylSupport.scalarCount.eq_1
assert_compatible GUT.BnvMixedWeylSupport.scalarField_spinTest => Physics.BnvMixedWeylSupport.scalarField_spinTest
assert_compatible GUT.BnvMixedWeylSupport.scalar_count_sum => Physics.BnvMixedWeylSupport.scalar_count_sum
assert_compatible GUT.BnvMixedWeylSupport.scalar_sum_weights => Physics.BnvMixedWeylSupport.scalar_sum_weights
assert_compatible GUT.BnvMixedWeylSupport.seven_support_of_nonzero => Physics.BnvMixedWeylSupport.seven_support_of_nonzero
