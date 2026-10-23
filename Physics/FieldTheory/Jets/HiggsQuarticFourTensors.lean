import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourTensors
import Physics.FieldTheory.Jets.HiggsQuarticFourInput
import Math.Algebra.ColoredQuarticSource
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourTensors instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourTensors.A => Physics.HiggsQuarticFourTensors.A,
  GUT.HiggsQuarticFourTensors.V => Physics.HiggsQuarticFourTensors.V,
  GUT.HiggsQuarticFourTensors.dirD_covariant => Physics.HiggsQuarticFourTensors.dirD_covariant,
  GUT.HiggsQuarticFourTensors.field_eq => Physics.HiggsQuarticFourTensors.field_eq,
  GUT.HiggsQuarticFourTensors.field_invariant => Physics.HiggsQuarticFourTensors.field_invariant,
  GUT.HiggsQuarticFourTensors.j1_covariant => Physics.HiggsQuarticFourTensors.j1_covariant,
  GUT.HiggsQuarticFourTensors.j2_covariant => Physics.HiggsQuarticFourTensors.j2_covariant,
  GUT.HiggsQuarticFourTensors.j3_covariant => Physics.HiggsQuarticFourTensors.j3_covariant,
  GUT.HiggsQuarticFourTensors.j4_covariant => Physics.HiggsQuarticFourTensors.j4_covariant,
  GUT.HiggsQuarticFourTensors.tensor_invariant => Physics.HiggsQuarticFourTensors.tensor_invariant,
  GUT.HiggsQuarticFourTensors.tensor_symmetric => Physics.HiggsQuarticFourTensors.tensor_symmetric,
  GUT.HiggsQuarticFourTensors.transport => Physics.HiggsQuarticFourTensors.transport,
  GUT.HiggsQuarticFourTensors.word_covariant => Physics.HiggsQuarticFourTensors.word_covariant
]

assert_compatible GUT.HiggsQuarticFourTensors.A => Physics.HiggsQuarticFourTensors.A
assert_compatible GUT.HiggsQuarticFourTensors.V => Physics.HiggsQuarticFourTensors.V
assert_compatible GUT.HiggsQuarticFourTensors.dirD_covariant => Physics.HiggsQuarticFourTensors.dirD_covariant
assert_compatible GUT.HiggsQuarticFourTensors.field_eq => Physics.HiggsQuarticFourTensors.field_eq
assert_compatible GUT.HiggsQuarticFourTensors.field_invariant => Physics.HiggsQuarticFourTensors.field_invariant
assert_compatible GUT.HiggsQuarticFourTensors.j1_covariant => Physics.HiggsQuarticFourTensors.j1_covariant
assert_compatible GUT.HiggsQuarticFourTensors.j2_covariant => Physics.HiggsQuarticFourTensors.j2_covariant
assert_compatible GUT.HiggsQuarticFourTensors.j3_covariant => Physics.HiggsQuarticFourTensors.j3_covariant
assert_compatible GUT.HiggsQuarticFourTensors.j4_covariant => Physics.HiggsQuarticFourTensors.j4_covariant
assert_compatible GUT.HiggsQuarticFourTensors.tensor_invariant => Physics.HiggsQuarticFourTensors.tensor_invariant
assert_compatible GUT.HiggsQuarticFourTensors.tensor_symmetric => Physics.HiggsQuarticFourTensors.tensor_symmetric
assert_compatible GUT.HiggsQuarticFourTensors.transport => Physics.HiggsQuarticFourTensors.transport
assert_compatible GUT.HiggsQuarticFourTensors.word_covariant => Physics.HiggsQuarticFourTensors.word_covariant
