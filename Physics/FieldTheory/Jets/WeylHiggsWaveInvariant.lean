import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveInvariant
import Physics.FieldTheory.Jets.WeylHiggsWaveInternal
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveInvariant instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsWaveInvariant.candidate_value => Physics.WeylHiggsWaveInvariant.candidate_value,
  GUT.WeylHiggsWaveInvariant.coefficient => Physics.WeylHiggsWaveInvariant.coefficient,
  GUT.WeylHiggsWaveInvariant.coefficient_apply => Physics.WeylHiggsWaveInvariant.coefficient_apply,
  GUT.WeylHiggsWaveInvariant.factorize => Physics.WeylHiggsWaveInvariant.factorize,
  GUT.WeylHiggsWaveInvariant.invariant => Physics.WeylHiggsWaveInvariant.invariant
]

assert_compatible GUT.WeylHiggsWaveInvariant.candidate_value => Physics.WeylHiggsWaveInvariant.candidate_value
assert_compatible GUT.WeylHiggsWaveInvariant.coefficient => Physics.WeylHiggsWaveInvariant.coefficient
assert_compatible GUT.WeylHiggsWaveInvariant.coefficient_apply => Physics.WeylHiggsWaveInvariant.coefficient_apply
assert_compatible GUT.WeylHiggsWaveInvariant.factorize => Physics.WeylHiggsWaveInvariant.factorize
assert_compatible GUT.WeylHiggsWaveInvariant.invariant => Physics.WeylHiggsWaveInvariant.invariant
