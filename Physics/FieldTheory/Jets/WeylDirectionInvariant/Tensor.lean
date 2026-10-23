import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Tensor
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Pairing
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Tensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylDirectionInvariant.canonical => Physics.WeylDirectionInvariant.canonical,
  GUT.WeylDirectionInvariant.canonical1 => Physics.WeylDirectionInvariant.canonical1,
  GUT.WeylDirectionInvariant.canonical1.eq_1 => Physics.WeylDirectionInvariant.canonical1.eq_1,
  GUT.WeylDirectionInvariant.canonical2 => Physics.WeylDirectionInvariant.canonical2,
  GUT.WeylDirectionInvariant.canonical2.eq_1 => Physics.WeylDirectionInvariant.canonical2.eq_1,
  GUT.WeylDirectionInvariant.canonical_apply => Physics.WeylDirectionInvariant.canonical_apply,
  GUT.WeylDirectionInvariant.invariant_of_components => Physics.WeylDirectionInvariant.invariant_of_components,
  GUT.WeylDirectionInvariant.invariant_of_transposed_components => Physics.WeylDirectionInvariant.invariant_of_transposed_components,
  GUT.WeylDirectionInvariant.spinVector_add_left => Physics.WeylDirectionInvariant.spinVector_add_left,
  GUT.WeylDirectionInvariant.spinVector_add_right => Physics.WeylDirectionInvariant.spinVector_add_right,
  GUT.WeylDirectionInvariant.spinVector_smul_left => Physics.WeylDirectionInvariant.spinVector_smul_left,
  GUT.WeylDirectionInvariant.spinVector_smul_right => Physics.WeylDirectionInvariant.spinVector_smul_right,
  GUT.WeylDirectionInvariant.tensor_ext => Physics.WeylDirectionInvariant.tensor_ext
]

assert_compatible GUT.WeylDirectionInvariant.canonical => Physics.WeylDirectionInvariant.canonical
assert_compatible GUT.WeylDirectionInvariant.canonical1 => Physics.WeylDirectionInvariant.canonical1
assert_compatible GUT.WeylDirectionInvariant.canonical1.eq_1 => Physics.WeylDirectionInvariant.canonical1.eq_1
assert_compatible GUT.WeylDirectionInvariant.canonical2 => Physics.WeylDirectionInvariant.canonical2
assert_compatible GUT.WeylDirectionInvariant.canonical2.eq_1 => Physics.WeylDirectionInvariant.canonical2.eq_1
assert_compatible GUT.WeylDirectionInvariant.canonical_apply => Physics.WeylDirectionInvariant.canonical_apply
assert_compatible GUT.WeylDirectionInvariant.invariant_of_components => Physics.WeylDirectionInvariant.invariant_of_components
assert_compatible GUT.WeylDirectionInvariant.invariant_of_transposed_components => Physics.WeylDirectionInvariant.invariant_of_transposed_components
assert_compatible GUT.WeylDirectionInvariant.spinVector_add_left => Physics.WeylDirectionInvariant.spinVector_add_left
assert_compatible GUT.WeylDirectionInvariant.spinVector_add_right => Physics.WeylDirectionInvariant.spinVector_add_right
assert_compatible GUT.WeylDirectionInvariant.spinVector_smul_left => Physics.WeylDirectionInvariant.spinVector_smul_left
assert_compatible GUT.WeylDirectionInvariant.spinVector_smul_right => Physics.WeylDirectionInvariant.spinVector_smul_right
assert_compatible GUT.WeylDirectionInvariant.tensor_ext => Physics.WeylDirectionInvariant.tensor_ext
