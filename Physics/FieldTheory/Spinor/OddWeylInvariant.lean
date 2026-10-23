import Physics.FieldTheory.Spinor.Tensors.OddWeylInvariant
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Tensors.OddWeylInvariant instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.OddWeylInvariant.Coefficient => Physics.OddWeylInvariant.Coefficient,
  GUT.OddWeylInvariant.eq_zero => Physics.OddWeylInvariant.eq_zero,
  GUT.OddWeylInvariant.external_eq_zero => Physics.OddWeylInvariant.external_eq_zero,
  GUT.OddWeylInvariant.left_three_eq_zero => Physics.OddWeylInvariant.left_three_eq_zero,
  GUT.OddWeylInvariant.odd_product_ne_one => Physics.OddWeylInvariant.odd_product_ne_one,
  GUT.OddWeylInvariant.representation => Physics.OddWeylInvariant.representation,
  GUT.OddWeylInvariant.representation.eq_1 => Physics.OddWeylInvariant.representation.eq_1,
  GUT.OddWeylInvariant.right_three_eq_zero => Physics.OddWeylInvariant.right_three_eq_zero,
  GUT.OddWeylInvariant.slotEigen => Physics.OddWeylInvariant.slotEigen,
  GUT.OddWeylInvariant.testElement => Physics.OddWeylInvariant.testElement,
  GUT.OddWeylInvariant.test_basis => Physics.OddWeylInvariant.test_basis
]

assert_compatible GUT.OddWeylInvariant.Coefficient => Physics.OddWeylInvariant.Coefficient
assert_compatible GUT.OddWeylInvariant.eq_zero => Physics.OddWeylInvariant.eq_zero
assert_compatible GUT.OddWeylInvariant.external_eq_zero => Physics.OddWeylInvariant.external_eq_zero
assert_compatible GUT.OddWeylInvariant.left_three_eq_zero => Physics.OddWeylInvariant.left_three_eq_zero
assert_compatible GUT.OddWeylInvariant.odd_product_ne_one => Physics.OddWeylInvariant.odd_product_ne_one
assert_compatible GUT.OddWeylInvariant.representation => Physics.OddWeylInvariant.representation
assert_compatible GUT.OddWeylInvariant.representation.eq_1 => Physics.OddWeylInvariant.representation.eq_1
assert_compatible GUT.OddWeylInvariant.right_three_eq_zero => Physics.OddWeylInvariant.right_three_eq_zero
assert_compatible GUT.OddWeylInvariant.slotEigen => Physics.OddWeylInvariant.slotEigen
assert_compatible GUT.OddWeylInvariant.testElement => Physics.OddWeylInvariant.testElement
assert_compatible GUT.OddWeylInvariant.test_basis => Physics.OddWeylInvariant.test_basis
