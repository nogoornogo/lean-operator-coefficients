import Physics.StandardModel.Operators.BaryonOne.Qque.S3QqueTensorSamples
import Physics.StandardModel.Operators.S3DipoleSelection
import Physics.StandardModel.Operators.QquePhysicalExteriorCompleteness
import Math.LinearAlgebra.SelectionCriteria
import Math.RepresentationTheory.FiniteFlavorControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.S3QqueTensorSamples instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.S3QqueTensorSamples.H => Physics.S3QqueTensorSamples.H,
  GUT.S3QqueTensorSamples.Residual => Physics.S3QqueTensorSamples.Residual,
  GUT.S3QqueTensorSamples.SymmetricResidual => Physics.S3QqueTensorSamples.SymmetricResidual,
  GUT.S3QqueTensorSamples.V => Physics.S3QqueTensorSamples.V,
  GUT.S3QqueTensorSamples.allowed_permutation_sign_sign => Physics.S3QqueTensorSamples.allowed_permutation_sign_sign,
  GUT.S3QqueTensorSamples.basis_expansion => Physics.S3QqueTensorSamples.basis_expansion,
  GUT.S3QqueTensorSamples.entry => Physics.S3QqueTensorSamples.entry,
  GUT.S3QqueTensorSamples.entry_swap => Physics.S3QqueTensorSamples.entry_swap,
  GUT.S3QqueTensorSamples.entry_symmetric => Physics.S3QqueTensorSamples.entry_symmetric,
  GUT.S3QqueTensorSamples.entry_zero => Physics.S3QqueTensorSamples.entry_zero,
  GUT.S3QqueTensorSamples.fin_one => Physics.S3QqueTensorSamples.fin_one,
  GUT.S3QqueTensorSamples.fin_two => Physics.S3QqueTensorSamples.fin_two,
  GUT.S3QqueTensorSamples.forbidden_permutation_trivial_sign => Physics.S3QqueTensorSamples.forbidden_permutation_trivial_sign,
  GUT.S3QqueTensorSamples.independent_flavor_preserves_sm => Physics.S3QqueTensorSamples.independent_flavor_preserves_sm,
  GUT.S3QqueTensorSamples.intertwiner_entry_zero => Physics.S3QqueTensorSamples.intertwiner_entry_zero,
  GUT.S3QqueTensorSamples.no_q_sign_equiv => Physics.S3QqueTensorSamples.no_q_sign_equiv,
  GUT.S3QqueTensorSamples.no_q_to_sign => Physics.S3QqueTensorSamples.no_q_to_sign,
  GUT.S3QqueTensorSamples.no_q_trivial_equiv => Physics.S3QqueTensorSamples.no_q_trivial_equiv,
  GUT.S3QqueTensorSamples.no_shared_q_sign => Physics.S3QqueTensorSamples.no_shared_q_sign,
  GUT.S3QqueTensorSamples.no_uniform_flavor_dictionary => Physics.S3QqueTensorSamples.no_uniform_flavor_dictionary,
  GUT.S3QqueTensorSamples.pairSum => Physics.S3QqueTensorSamples.pairSum,
  GUT.S3QqueTensorSamples.pairSum_tmul => Physics.S3QqueTensorSamples.pairSum_tmul,
  GUT.S3QqueTensorSamples.positiveCoefficient => Physics.S3QqueTensorSamples.positiveCoefficient,
  GUT.S3QqueTensorSamples.positiveResidual => Physics.S3QqueTensorSamples.positiveResidual,
  GUT.S3QqueTensorSamples.positive_nonzero => Physics.S3QqueTensorSamples.positive_nonzero,
  GUT.S3QqueTensorSamples.positive_witness => Physics.S3QqueTensorSamples.positive_witness,
  GUT.S3QqueTensorSamples.q => Physics.S3QqueTensorSamples.q,
  GUT.S3QqueTensorSamples.q_to_trivial_not_injective => Physics.S3QqueTensorSamples.q_to_trivial_not_injective,
  GUT.S3QqueTensorSamples.q_unit => Physics.S3QqueTensorSamples.q_unit,
  GUT.S3QqueTensorSamples.residual_zero => Physics.S3QqueTensorSamples.residual_zero,
  GUT.S3QqueTensorSamples.sign => Physics.S3QqueTensorSamples.sign,
  GUT.S3QqueTensorSamples.signCharacter => Physics.S3QqueTensorSamples.signCharacter,
  GUT.S3QqueTensorSamples.signCharacter.eq_1 => Physics.S3QqueTensorSamples.signCharacter.eq_1,
  GUT.S3QqueTensorSamples.sign_apply => Physics.S3QqueTensorSamples.sign_apply,
  GUT.S3QqueTensorSamples.sign_square => Physics.S3QqueTensorSamples.sign_square,
  GUT.S3QqueTensorSamples.sign_swap => Physics.S3QqueTensorSamples.sign_swap,
  GUT.S3QqueTensorSamples.trivial => Physics.S3QqueTensorSamples.trivial,
  GUT.S3QqueTensorSamples.unit => Physics.S3QqueTensorSamples.unit,
  GUT.S3QqueTensorSamples.unit.eq_1 => Physics.S3QqueTensorSamples.unit.eq_1
]

assert_compatible GUT.S3QqueTensorSamples.H => Physics.S3QqueTensorSamples.H
assert_compatible GUT.S3QqueTensorSamples.Residual => Physics.S3QqueTensorSamples.Residual
assert_compatible GUT.S3QqueTensorSamples.SymmetricResidual => Physics.S3QqueTensorSamples.SymmetricResidual
assert_compatible GUT.S3QqueTensorSamples.V => Physics.S3QqueTensorSamples.V
assert_compatible GUT.S3QqueTensorSamples.allowed_permutation_sign_sign => Physics.S3QqueTensorSamples.allowed_permutation_sign_sign
assert_compatible GUT.S3QqueTensorSamples.basis_expansion => Physics.S3QqueTensorSamples.basis_expansion
assert_compatible GUT.S3QqueTensorSamples.entry => Physics.S3QqueTensorSamples.entry
assert_compatible GUT.S3QqueTensorSamples.entry_swap => Physics.S3QqueTensorSamples.entry_swap
assert_compatible GUT.S3QqueTensorSamples.entry_symmetric => Physics.S3QqueTensorSamples.entry_symmetric
assert_compatible GUT.S3QqueTensorSamples.entry_zero => Physics.S3QqueTensorSamples.entry_zero
assert_compatible GUT.S3QqueTensorSamples.fin_one => Physics.S3QqueTensorSamples.fin_one
assert_compatible GUT.S3QqueTensorSamples.fin_two => Physics.S3QqueTensorSamples.fin_two
assert_compatible GUT.S3QqueTensorSamples.forbidden_permutation_trivial_sign => Physics.S3QqueTensorSamples.forbidden_permutation_trivial_sign
assert_compatible GUT.S3QqueTensorSamples.independent_flavor_preserves_sm => Physics.S3QqueTensorSamples.independent_flavor_preserves_sm
assert_compatible GUT.S3QqueTensorSamples.intertwiner_entry_zero => Physics.S3QqueTensorSamples.intertwiner_entry_zero
assert_compatible GUT.S3QqueTensorSamples.no_q_sign_equiv => Physics.S3QqueTensorSamples.no_q_sign_equiv
assert_compatible GUT.S3QqueTensorSamples.no_q_to_sign => Physics.S3QqueTensorSamples.no_q_to_sign
assert_compatible GUT.S3QqueTensorSamples.no_q_trivial_equiv => Physics.S3QqueTensorSamples.no_q_trivial_equiv
assert_compatible GUT.S3QqueTensorSamples.no_shared_q_sign => Physics.S3QqueTensorSamples.no_shared_q_sign
assert_compatible GUT.S3QqueTensorSamples.no_uniform_flavor_dictionary => Physics.S3QqueTensorSamples.no_uniform_flavor_dictionary
assert_compatible GUT.S3QqueTensorSamples.pairSum => Physics.S3QqueTensorSamples.pairSum
assert_compatible GUT.S3QqueTensorSamples.pairSum_tmul => Physics.S3QqueTensorSamples.pairSum_tmul
assert_compatible GUT.S3QqueTensorSamples.positiveCoefficient => Physics.S3QqueTensorSamples.positiveCoefficient
assert_compatible GUT.S3QqueTensorSamples.positiveResidual => Physics.S3QqueTensorSamples.positiveResidual
assert_compatible GUT.S3QqueTensorSamples.positive_nonzero => Physics.S3QqueTensorSamples.positive_nonzero
assert_compatible GUT.S3QqueTensorSamples.positive_witness => Physics.S3QqueTensorSamples.positive_witness
assert_compatible GUT.S3QqueTensorSamples.q => Physics.S3QqueTensorSamples.q
assert_compatible GUT.S3QqueTensorSamples.q_to_trivial_not_injective => Physics.S3QqueTensorSamples.q_to_trivial_not_injective
assert_compatible GUT.S3QqueTensorSamples.q_unit => Physics.S3QqueTensorSamples.q_unit
assert_compatible GUT.S3QqueTensorSamples.residual_zero => Physics.S3QqueTensorSamples.residual_zero
assert_compatible GUT.S3QqueTensorSamples.sign => Physics.S3QqueTensorSamples.sign
assert_compatible GUT.S3QqueTensorSamples.signCharacter => Physics.S3QqueTensorSamples.signCharacter
assert_compatible GUT.S3QqueTensorSamples.signCharacter.eq_1 => Physics.S3QqueTensorSamples.signCharacter.eq_1
assert_compatible GUT.S3QqueTensorSamples.sign_apply => Physics.S3QqueTensorSamples.sign_apply
assert_compatible GUT.S3QqueTensorSamples.sign_square => Physics.S3QqueTensorSamples.sign_square
assert_compatible GUT.S3QqueTensorSamples.sign_swap => Physics.S3QqueTensorSamples.sign_swap
assert_compatible GUT.S3QqueTensorSamples.trivial => Physics.S3QqueTensorSamples.trivial
assert_compatible GUT.S3QqueTensorSamples.unit => Physics.S3QqueTensorSamples.unit
assert_compatible GUT.S3QqueTensorSamples.unit.eq_1 => Physics.S3QqueTensorSamples.unit.eq_1
