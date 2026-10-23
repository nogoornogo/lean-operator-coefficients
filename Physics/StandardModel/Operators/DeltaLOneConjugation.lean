import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneConjugation
import Physics.StandardModel.Operators.DeltaLOneSignedInput
import Math.RepresentationTheory.ExteriorConjugation
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneConjugation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaLOneConjugation.conjugateSpecies => Physics.DeltaLOneConjugation.conjugateSpecies,
  GUT.DeltaLOneConjugation.conjugate_degree => Physics.DeltaLOneConjugation.conjugate_degree,
  GUT.DeltaLOneConjugation.conjugate_mem => Physics.DeltaLOneConjugation.conjugate_mem,
  GUT.DeltaLOneConjugation.equiv => Physics.DeltaLOneConjugation.equiv,
  GUT.DeltaLOneConjugation.lepton_conjugate => Physics.DeltaLOneConjugation.lepton_conjugate,
  GUT.DeltaLOneConjugation.nonzero_iff => Physics.DeltaLOneConjugation.nonzero_iff
]

assert_compatible GUT.DeltaLOneConjugation.conjugateSpecies => Physics.DeltaLOneConjugation.conjugateSpecies
assert_compatible GUT.DeltaLOneConjugation.conjugate_degree => Physics.DeltaLOneConjugation.conjugate_degree
assert_compatible GUT.DeltaLOneConjugation.conjugate_mem => Physics.DeltaLOneConjugation.conjugate_mem
assert_compatible GUT.DeltaLOneConjugation.equiv => Physics.DeltaLOneConjugation.equiv
assert_compatible GUT.DeltaLOneConjugation.lepton_conjugate => Physics.DeltaLOneConjugation.lepton_conjugate
assert_compatible GUT.DeltaLOneConjugation.nonzero_iff => Physics.DeltaLOneConjugation.nonzero_iff
