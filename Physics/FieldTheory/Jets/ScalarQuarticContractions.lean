import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticContractions
import Physics.FieldTheory.Jets.ScalarQuarticFourWitness
import Physics.FieldTheory.Jets.ScalarQuarticTwoCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticContractions instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarQuarticContractions.A => Physics.ScalarQuarticContractions.A,
  GUT.ScalarQuarticContractions.A.eq_1 => Physics.ScalarQuarticContractions.A.eq_1,
  GUT.ScalarQuarticContractions.A_eq_C4 => Physics.ScalarQuarticContractions.A_eq_C4,
  GUT.ScalarQuarticContractions.A_nonzero => Physics.ScalarQuarticContractions.A_nonzero,
  GUT.ScalarQuarticContractions.A_relation => Physics.ScalarQuarticContractions.A_relation,
  GUT.ScalarQuarticContractions.B => Physics.ScalarQuarticContractions.B,
  GUT.ScalarQuarticContractions.B.eq_1 => Physics.ScalarQuarticContractions.B.eq_1,
  GUT.ScalarQuarticContractions.B_eq_C4 => Physics.ScalarQuarticContractions.B_eq_C4,
  GUT.ScalarQuarticContractions.B_nonzero => Physics.ScalarQuarticContractions.B_nonzero,
  GUT.ScalarQuarticContractions.C4 => Physics.ScalarQuarticContractions.C4,
  GUT.ScalarQuarticContractions.C4_fixed => Physics.ScalarQuarticContractions.C4_fixed,
  GUT.ScalarQuarticContractions.C4_relation => Physics.ScalarQuarticContractions.C4_relation,
  GUT.ScalarQuarticContractions.K => Physics.ScalarQuarticContractions.K,
  GUT.ScalarQuarticContractions.W => Physics.ScalarQuarticContractions.W,
  GUT.ScalarQuarticContractions.candidateImage => Physics.ScalarQuarticContractions.candidateImage,
  GUT.ScalarQuarticContractions.candidateImage.eq_1 => Physics.ScalarQuarticContractions.candidateImage.eq_1,
  GUT.ScalarQuarticContractions.candidateSource => Physics.ScalarQuarticContractions.candidateSource,
  GUT.ScalarQuarticContractions.candidateSource.eq_1 => Physics.ScalarQuarticContractions.candidateSource.eq_1,
  GUT.ScalarQuarticContractions.candidate_grade => Physics.ScalarQuarticContractions.candidate_grade,
  GUT.ScalarQuarticContractions.candidate_image_dimension => Physics.ScalarQuarticContractions.candidate_image_dimension,
  GUT.ScalarQuarticContractions.candidate_image_eq => Physics.ScalarQuarticContractions.candidate_image_eq,
  GUT.ScalarQuarticContractions.candidate_image_fixed => Physics.ScalarQuarticContractions.candidate_image_fixed,
  GUT.ScalarQuarticContractions.differentiated_inner => Physics.ScalarQuarticContractions.differentiated_inner,
  GUT.ScalarQuarticContractions.divergence_zero => Physics.ScalarQuarticContractions.divergence_zero,
  GUT.ScalarQuarticContractions.eta => Physics.ScalarQuarticContractions.eta,
  GUT.ScalarQuarticContractions.ideal_zero => Physics.ScalarQuarticContractions.ideal_zero,
  GUT.ScalarQuarticContractions.kinetic_sum => Physics.ScalarQuarticContractions.kinetic_sum,
  GUT.ScalarQuarticContractions.q => Physics.ScalarQuarticContractions.q,
  GUT.ScalarQuarticContractions.third_commute => Physics.ScalarQuarticContractions.third_commute,
  GUT.ScalarQuarticContractions.wave_mem => Physics.ScalarQuarticContractions.wave_mem,
  GUT.ScalarQuarticContractions.wave_sum => Physics.ScalarQuarticContractions.wave_sum
]

assert_compatible GUT.ScalarQuarticContractions.A => Physics.ScalarQuarticContractions.A
assert_compatible GUT.ScalarQuarticContractions.A.eq_1 => Physics.ScalarQuarticContractions.A.eq_1
assert_compatible GUT.ScalarQuarticContractions.A_eq_C4 => Physics.ScalarQuarticContractions.A_eq_C4
assert_compatible GUT.ScalarQuarticContractions.A_nonzero => Physics.ScalarQuarticContractions.A_nonzero
assert_compatible GUT.ScalarQuarticContractions.A_relation => Physics.ScalarQuarticContractions.A_relation
assert_compatible GUT.ScalarQuarticContractions.B => Physics.ScalarQuarticContractions.B
assert_compatible GUT.ScalarQuarticContractions.B.eq_1 => Physics.ScalarQuarticContractions.B.eq_1
assert_compatible GUT.ScalarQuarticContractions.B_eq_C4 => Physics.ScalarQuarticContractions.B_eq_C4
assert_compatible GUT.ScalarQuarticContractions.B_nonzero => Physics.ScalarQuarticContractions.B_nonzero
assert_compatible GUT.ScalarQuarticContractions.C4 => Physics.ScalarQuarticContractions.C4
assert_compatible GUT.ScalarQuarticContractions.C4_fixed => Physics.ScalarQuarticContractions.C4_fixed
assert_compatible GUT.ScalarQuarticContractions.C4_relation => Physics.ScalarQuarticContractions.C4_relation
assert_compatible GUT.ScalarQuarticContractions.K => Physics.ScalarQuarticContractions.K
assert_compatible GUT.ScalarQuarticContractions.W => Physics.ScalarQuarticContractions.W
assert_compatible GUT.ScalarQuarticContractions.candidateImage => Physics.ScalarQuarticContractions.candidateImage
assert_compatible GUT.ScalarQuarticContractions.candidateImage.eq_1 => Physics.ScalarQuarticContractions.candidateImage.eq_1
assert_compatible GUT.ScalarQuarticContractions.candidateSource => Physics.ScalarQuarticContractions.candidateSource
assert_compatible GUT.ScalarQuarticContractions.candidateSource.eq_1 => Physics.ScalarQuarticContractions.candidateSource.eq_1
assert_compatible GUT.ScalarQuarticContractions.candidate_grade => Physics.ScalarQuarticContractions.candidate_grade
assert_compatible GUT.ScalarQuarticContractions.candidate_image_dimension => Physics.ScalarQuarticContractions.candidate_image_dimension
assert_compatible GUT.ScalarQuarticContractions.candidate_image_eq => Physics.ScalarQuarticContractions.candidate_image_eq
assert_compatible GUT.ScalarQuarticContractions.candidate_image_fixed => Physics.ScalarQuarticContractions.candidate_image_fixed
assert_compatible GUT.ScalarQuarticContractions.differentiated_inner => Physics.ScalarQuarticContractions.differentiated_inner
assert_compatible GUT.ScalarQuarticContractions.divergence_zero => Physics.ScalarQuarticContractions.divergence_zero
assert_compatible GUT.ScalarQuarticContractions.eta => Physics.ScalarQuarticContractions.eta
assert_compatible GUT.ScalarQuarticContractions.ideal_zero => Physics.ScalarQuarticContractions.ideal_zero
assert_compatible GUT.ScalarQuarticContractions.kinetic_sum => Physics.ScalarQuarticContractions.kinetic_sum
assert_compatible GUT.ScalarQuarticContractions.q => Physics.ScalarQuarticContractions.q
assert_compatible GUT.ScalarQuarticContractions.third_commute => Physics.ScalarQuarticContractions.third_commute
assert_compatible GUT.ScalarQuarticContractions.wave_mem => Physics.ScalarQuarticContractions.wave_mem
assert_compatible GUT.ScalarQuarticContractions.wave_sum => Physics.ScalarQuarticContractions.wave_sum
