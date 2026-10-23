import Physics.StandardModel.Operators.BaryonOne.Qque.QqueCommonIrreducible
import Physics.StandardModel.Operators.FullLightRadicalQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.QqueCommonIrreducible instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueCommonIrreducible.FullShares => Physics.QqueCommonIrreducible.FullShares,
  GUT.QqueCommonIrreducible.Shares => Physics.QqueCommonIrreducible.Shares,
  GUT.QqueCommonIrreducible.coefficient_iff => Physics.QqueCommonIrreducible.coefficient_iff,
  GUT.QqueCommonIrreducible.coefficient_iff_of_compact => Physics.QqueCommonIrreducible.coefficient_iff_of_compact,
  GUT.QqueCommonIrreducible.full_forbidden_iff => Physics.QqueCommonIrreducible.full_forbidden_iff,
  GUT.QqueCommonIrreducible.full_nonzero_iff => Physics.QqueCommonIrreducible.full_nonzero_iff,
  GUT.QqueCommonIrreducible.full_nonzero_iff_of_compact => Physics.QqueCommonIrreducible.full_nonzero_iff_of_compact,
  GUT.QqueCommonIrreducible.full_square_semisimple => Physics.QqueCommonIrreducible.full_square_semisimple,
  GUT.QqueCommonIrreducible.hom_iff => Physics.QqueCommonIrreducible.hom_iff,
  GUT.QqueCommonIrreducible.radical_forbidden_iff => Physics.QqueCommonIrreducible.radical_forbidden_iff,
  GUT.QqueCommonIrreducible.radical_nonzero_iff => Physics.QqueCommonIrreducible.radical_nonzero_iff
]

assert_compatible GUT.QqueCommonIrreducible.FullShares => Physics.QqueCommonIrreducible.FullShares
assert_compatible GUT.QqueCommonIrreducible.Shares => Physics.QqueCommonIrreducible.Shares
assert_compatible GUT.QqueCommonIrreducible.coefficient_iff => Physics.QqueCommonIrreducible.coefficient_iff
assert_compatible GUT.QqueCommonIrreducible.coefficient_iff_of_compact => Physics.QqueCommonIrreducible.coefficient_iff_of_compact
assert_compatible GUT.QqueCommonIrreducible.full_forbidden_iff => Physics.QqueCommonIrreducible.full_forbidden_iff
assert_compatible GUT.QqueCommonIrreducible.full_nonzero_iff => Physics.QqueCommonIrreducible.full_nonzero_iff
assert_compatible GUT.QqueCommonIrreducible.full_nonzero_iff_of_compact => Physics.QqueCommonIrreducible.full_nonzero_iff_of_compact
assert_compatible GUT.QqueCommonIrreducible.full_square_semisimple => Physics.QqueCommonIrreducible.full_square_semisimple
assert_compatible GUT.QqueCommonIrreducible.hom_iff => Physics.QqueCommonIrreducible.hom_iff
assert_compatible GUT.QqueCommonIrreducible.radical_forbidden_iff => Physics.QqueCommonIrreducible.radical_forbidden_iff
assert_compatible GUT.QqueCommonIrreducible.radical_nonzero_iff => Physics.QqueCommonIrreducible.radical_nonzero_iff
