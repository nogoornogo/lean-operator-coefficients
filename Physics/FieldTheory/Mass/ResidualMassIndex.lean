import Physics.FieldTheory.Mass.Spectrum.ResidualMassIndex
import Physics.FieldTheory.Mass.ConjugationMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Spectrum.ResidualMassIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ResidualMassIndex.light_torus_unitary => Physics.ResidualMassIndex.light_torus_unitary,
  GUT.ResidualMassIndex.weight_index_invariant => Physics.ResidualMassIndex.weight_index_invariant
]

assert_compatible GUT.ResidualMassIndex.light_torus_unitary => Physics.ResidualMassIndex.light_torus_unitary
assert_compatible GUT.ResidualMassIndex.weight_index_invariant => Physics.ResidualMassIndex.weight_index_invariant
