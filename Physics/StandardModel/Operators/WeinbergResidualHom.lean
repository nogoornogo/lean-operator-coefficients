import Physics.StandardModel.Operators.Weinberg.WeinbergResidualHom
import Physics.FieldTheory.Spinor.WeylPairInvariant
import Physics.StandardModel.Gauge.WeinbergWeakInvariant
import Math.RepresentationTheory.NormalizedInvariantFactor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.WeinbergResidualHom instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeinbergResidualHom.Coefficient => Physics.WeinbergResidualHom.Coefficient,
  GUT.WeinbergResidualHom.HasFermionExchange => Physics.WeinbergResidualHom.HasFermionExchange,
  GUT.WeinbergResidualHom.Residual => Physics.WeinbergResidualHom.Residual,
  GUT.WeinbergResidualHom.eq_zero_of_subsingleton => Physics.WeinbergResidualHom.eq_zero_of_subsingleton,
  GUT.WeinbergResidualHom.exchange_iff => Physics.WeinbergResidualHom.exchange_iff,
  GUT.WeinbergResidualHom.exists_nonzero_iff => Physics.WeinbergResidualHom.exists_nonzero_iff,
  GUT.WeinbergResidualHom.factorEquiv => Physics.WeinbergResidualHom.factorEquiv,
  GUT.WeinbergResidualHom.homEquiv => Physics.WeinbergResidualHom.homEquiv,
  GUT.WeinbergResidualHom.input => Physics.WeinbergResidualHom.input,
  GUT.WeinbergResidualHom.localContraction => Physics.WeinbergResidualHom.localContraction,
  GUT.WeinbergResidualHom.localContraction.eq_1 => Physics.WeinbergResidualHom.localContraction.eq_1,
  GUT.WeinbergResidualHom.localRepresentation => Physics.WeinbergResidualHom.localRepresentation,
  GUT.WeinbergResidualHom.localWitness => Physics.WeinbergResidualHom.localWitness,
  GUT.WeinbergResidualHom.localWitness.eq_1 => Physics.WeinbergResidualHom.localWitness.eq_1,
  GUT.WeinbergResidualHom.local_normalized => Physics.WeinbergResidualHom.local_normalized,
  GUT.WeinbergResidualHom.local_unique => Physics.WeinbergResidualHom.local_unique,
  GUT.WeinbergResidualHom.reconstruction => Physics.WeinbergResidualHom.reconstruction,
  GUT.WeinbergResidualHom.sector => Physics.WeinbergResidualHom.sector,
  GUT.WeinbergResidualHom.symmetricEquiv => Physics.WeinbergResidualHom.symmetricEquiv
]

assert_compatible GUT.WeinbergResidualHom.Coefficient => Physics.WeinbergResidualHom.Coefficient
assert_compatible GUT.WeinbergResidualHom.HasFermionExchange => Physics.WeinbergResidualHom.HasFermionExchange
assert_compatible GUT.WeinbergResidualHom.Residual => Physics.WeinbergResidualHom.Residual
assert_compatible GUT.WeinbergResidualHom.eq_zero_of_subsingleton => Physics.WeinbergResidualHom.eq_zero_of_subsingleton
assert_compatible GUT.WeinbergResidualHom.exchange_iff => Physics.WeinbergResidualHom.exchange_iff
assert_compatible GUT.WeinbergResidualHom.exists_nonzero_iff => Physics.WeinbergResidualHom.exists_nonzero_iff
assert_compatible GUT.WeinbergResidualHom.factorEquiv => Physics.WeinbergResidualHom.factorEquiv
assert_compatible GUT.WeinbergResidualHom.homEquiv => Physics.WeinbergResidualHom.homEquiv
assert_compatible GUT.WeinbergResidualHom.input => Physics.WeinbergResidualHom.input
assert_compatible GUT.WeinbergResidualHom.localContraction => Physics.WeinbergResidualHom.localContraction
assert_compatible GUT.WeinbergResidualHom.localContraction.eq_1 => Physics.WeinbergResidualHom.localContraction.eq_1
assert_compatible GUT.WeinbergResidualHom.localRepresentation => Physics.WeinbergResidualHom.localRepresentation
assert_compatible GUT.WeinbergResidualHom.localWitness => Physics.WeinbergResidualHom.localWitness
assert_compatible GUT.WeinbergResidualHom.localWitness.eq_1 => Physics.WeinbergResidualHom.localWitness.eq_1
assert_compatible GUT.WeinbergResidualHom.local_normalized => Physics.WeinbergResidualHom.local_normalized
assert_compatible GUT.WeinbergResidualHom.local_unique => Physics.WeinbergResidualHom.local_unique
assert_compatible GUT.WeinbergResidualHom.reconstruction => Physics.WeinbergResidualHom.reconstruction
assert_compatible GUT.WeinbergResidualHom.sector => Physics.WeinbergResidualHom.sector
assert_compatible GUT.WeinbergResidualHom.symmetricEquiv => Physics.WeinbergResidualHom.symmetricEquiv
