import Physics.FieldTheory.Spinor.Weyl.WeylSpinorUniqueness
import Physics.FieldTheory.Spinor.WeylSpinor
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.WeylSpinorUniqueness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylSpinor.left.eq_1 => Physics.WeylSpinor.left.eq_1,
  GUT.WeylSpinorUniqueness.Coefficient => Physics.WeylSpinorUniqueness.Coefficient,
  GUT.WeylSpinorUniqueness.basisValue => Physics.WeylSpinorUniqueness.basisValue,
  GUT.WeylSpinorUniqueness.basisValue_formula => Physics.WeylSpinorUniqueness.basisValue_formula,
  GUT.WeylSpinorUniqueness.basisValue_swap_left => Physics.WeylSpinorUniqueness.basisValue_swap_left,
  GUT.WeylSpinorUniqueness.basisValue_swap_right => Physics.WeylSpinorUniqueness.basisValue_swap_right,
  GUT.WeylSpinorUniqueness.basisValue_vanish => Physics.WeylSpinorUniqueness.basisValue_vanish,
  GUT.WeylSpinorUniqueness.eq_smul_four => Physics.WeylSpinorUniqueness.eq_smul_four
]

assert_compatible GUT.WeylSpinor.left.eq_1 => Physics.WeylSpinor.left.eq_1
assert_compatible GUT.WeylSpinorUniqueness.Coefficient => Physics.WeylSpinorUniqueness.Coefficient
assert_compatible GUT.WeylSpinorUniqueness.basisValue => Physics.WeylSpinorUniqueness.basisValue
assert_compatible GUT.WeylSpinorUniqueness.basisValue_formula => Physics.WeylSpinorUniqueness.basisValue_formula
assert_compatible GUT.WeylSpinorUniqueness.basisValue_swap_left => Physics.WeylSpinorUniqueness.basisValue_swap_left
assert_compatible GUT.WeylSpinorUniqueness.basisValue_swap_right => Physics.WeylSpinorUniqueness.basisValue_swap_right
assert_compatible GUT.WeylSpinorUniqueness.basisValue_vanish => Physics.WeylSpinorUniqueness.basisValue_vanish
assert_compatible GUT.WeylSpinorUniqueness.eq_smul_four => Physics.WeylSpinorUniqueness.eq_smul_four
