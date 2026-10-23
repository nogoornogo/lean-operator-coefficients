import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Pairing
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Basic
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Pairing instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylDirectionInvariant.S.eq_1 => Physics.WeylDirectionInvariant.S.eq_1,
  GUT.WeylDirectionInvariant.contraction => Physics.WeylDirectionInvariant.contraction,
  GUT.WeylDirectionInvariant.contraction.eq_1 => Physics.WeylDirectionInvariant.contraction.eq_1,
  GUT.WeylDirectionInvariant.contraction_basis => Physics.WeylDirectionInvariant.contraction_basis,
  GUT.WeylDirectionInvariant.contraction_invariant => Physics.WeylDirectionInvariant.contraction_invariant,
  GUT.WeylDirectionInvariant.pair => Physics.WeylDirectionInvariant.pair,
  GUT.WeylDirectionInvariant.pair.eq_1 => Physics.WeylDirectionInvariant.pair.eq_1,
  GUT.WeylDirectionInvariant.pair_dual => Physics.WeylDirectionInvariant.pair_dual,
  GUT.WeylDirectionInvariant.pair_invariant => Physics.WeylDirectionInvariant.pair_invariant,
  GUT.WeylDirectionInvariant.pauli_from => Physics.WeylDirectionInvariant.pauli_from,
  GUT.WeylDirectionInvariant.spinVector => Physics.WeylDirectionInvariant.spinVector,
  GUT.WeylDirectionInvariant.spinVector.eq_1 => Physics.WeylDirectionInvariant.spinVector.eq_1,
  GUT.WeylDirectionInvariant.spinVector_covariant => Physics.WeylDirectionInvariant.spinVector_covariant
]

assert_compatible GUT.WeylDirectionInvariant.S.eq_1 => Physics.WeylDirectionInvariant.S.eq_1
assert_compatible GUT.WeylDirectionInvariant.contraction => Physics.WeylDirectionInvariant.contraction
assert_compatible GUT.WeylDirectionInvariant.contraction.eq_1 => Physics.WeylDirectionInvariant.contraction.eq_1
assert_compatible GUT.WeylDirectionInvariant.contraction_basis => Physics.WeylDirectionInvariant.contraction_basis
assert_compatible GUT.WeylDirectionInvariant.contraction_invariant => Physics.WeylDirectionInvariant.contraction_invariant
assert_compatible GUT.WeylDirectionInvariant.pair => Physics.WeylDirectionInvariant.pair
assert_compatible GUT.WeylDirectionInvariant.pair.eq_1 => Physics.WeylDirectionInvariant.pair.eq_1
assert_compatible GUT.WeylDirectionInvariant.pair_dual => Physics.WeylDirectionInvariant.pair_dual
assert_compatible GUT.WeylDirectionInvariant.pair_invariant => Physics.WeylDirectionInvariant.pair_invariant
assert_compatible GUT.WeylDirectionInvariant.pauli_from => Physics.WeylDirectionInvariant.pauli_from
assert_compatible GUT.WeylDirectionInvariant.spinVector => Physics.WeylDirectionInvariant.spinVector
assert_compatible GUT.WeylDirectionInvariant.spinVector.eq_1 => Physics.WeylDirectionInvariant.spinVector.eq_1
assert_compatible GUT.WeylDirectionInvariant.spinVector_covariant => Physics.WeylDirectionInvariant.spinVector_covariant
