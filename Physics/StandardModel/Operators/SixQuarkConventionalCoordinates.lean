import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalCoordinates
import Physics.StandardModel.Operators.SixQuarkConventionalBasis
import Math.RepresentationTheory.SixSlotSpeciesSum
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SixQuarkConventionalBasis.O1.eq_1 => Physics.SixQuarkConventionalBasis.O1.eq_1,
  GUT.SixQuarkConventionalBasis.O2.eq_1 => Physics.SixQuarkConventionalBasis.O2.eq_1,
  GUT.SixQuarkConventionalBasis.O3.eq_1 => Physics.SixQuarkConventionalBasis.O3.eq_1,
  GUT.SixQuarkConventionalBasis.descend.congr_simp => Physics.SixQuarkConventionalBasis.descend.congr_simp,
  GUT.SixQuarkConventionalCoordinates.O1_block => Physics.SixQuarkConventionalCoordinates.O1_block,
  GUT.SixQuarkConventionalCoordinates.O2_block => Physics.SixQuarkConventionalCoordinates.O2_block,
  GUT.SixQuarkConventionalCoordinates.O3_block => Physics.SixQuarkConventionalCoordinates.O3_block,
  GUT.SixQuarkConventionalCoordinates.Q1 => Physics.SixQuarkConventionalCoordinates.Q1,
  GUT.SixQuarkConventionalCoordinates.Q1.eq_1 => Physics.SixQuarkConventionalCoordinates.Q1.eq_1,
  GUT.SixQuarkConventionalCoordinates.Q4 => Physics.SixQuarkConventionalCoordinates.Q4,
  GUT.SixQuarkConventionalCoordinates.Q4.eq_1 => Physics.SixQuarkConventionalCoordinates.Q4.eq_1,
  GUT.SixQuarkConventionalCoordinates.blockAlternation_eq => Physics.SixQuarkConventionalCoordinates.blockAlternation_eq,
  GUT.SixQuarkConventionalCoordinates.chiralEquiv => Physics.SixQuarkConventionalCoordinates.chiralEquiv,
  GUT.SixQuarkConventionalCoordinates.conventionalEquiv => Physics.SixQuarkConventionalCoordinates.conventionalEquiv,
  GUT.SixQuarkConventionalCoordinates.conventional_determinant => Physics.SixQuarkConventionalCoordinates.conventional_determinant,
  GUT.SixQuarkConventionalCoordinates.descend_block => Physics.SixQuarkConventionalCoordinates.descend_block,
  GUT.SixQuarkConventionalCoordinates.fierz => Physics.SixQuarkConventionalCoordinates.fierz,
  GUT.SixQuarkConventionalCoordinates.probes_O1 => Physics.SixQuarkConventionalCoordinates.probes_O1,
  GUT.SixQuarkConventionalCoordinates.probes_O2 => Physics.SixQuarkConventionalCoordinates.probes_O2,
  GUT.SixQuarkConventionalCoordinates.probes_O3 => Physics.SixQuarkConventionalCoordinates.probes_O3,
  GUT.SixQuarkConventionalCoordinates.probes_Q1 => Physics.SixQuarkConventionalCoordinates.probes_Q1,
  GUT.SixQuarkConventionalCoordinates.probes_Q4 => Physics.SixQuarkConventionalCoordinates.probes_Q4,
  GUT.SixQuarkConventionalCoordinates.reconstruct => Physics.SixQuarkConventionalCoordinates.reconstruct,
  GUT.SixQuarkConventionalCoordinates.reconstruct_chiral => Physics.SixQuarkConventionalCoordinates.reconstruct_chiral,
  GUT.SixQuarkSpeciesQuotient.twoProbes.eq_1 => Physics.SixQuarkSpeciesQuotient.twoProbes.eq_1
]

assert_compatible GUT.SixQuarkConventionalBasis.O1.eq_1 => Physics.SixQuarkConventionalBasis.O1.eq_1
assert_compatible GUT.SixQuarkConventionalBasis.O2.eq_1 => Physics.SixQuarkConventionalBasis.O2.eq_1
assert_compatible GUT.SixQuarkConventionalBasis.O3.eq_1 => Physics.SixQuarkConventionalBasis.O3.eq_1
assert_compatible GUT.SixQuarkConventionalBasis.descend.congr_simp => Physics.SixQuarkConventionalBasis.descend.congr_simp
assert_compatible GUT.SixQuarkConventionalCoordinates.O1_block => Physics.SixQuarkConventionalCoordinates.O1_block
assert_compatible GUT.SixQuarkConventionalCoordinates.O2_block => Physics.SixQuarkConventionalCoordinates.O2_block
assert_compatible GUT.SixQuarkConventionalCoordinates.O3_block => Physics.SixQuarkConventionalCoordinates.O3_block
assert_compatible GUT.SixQuarkConventionalCoordinates.Q1 => Physics.SixQuarkConventionalCoordinates.Q1
assert_compatible GUT.SixQuarkConventionalCoordinates.Q1.eq_1 => Physics.SixQuarkConventionalCoordinates.Q1.eq_1
assert_compatible GUT.SixQuarkConventionalCoordinates.Q4 => Physics.SixQuarkConventionalCoordinates.Q4
assert_compatible GUT.SixQuarkConventionalCoordinates.Q4.eq_1 => Physics.SixQuarkConventionalCoordinates.Q4.eq_1
assert_compatible GUT.SixQuarkConventionalCoordinates.blockAlternation_eq => Physics.SixQuarkConventionalCoordinates.blockAlternation_eq
assert_compatible GUT.SixQuarkConventionalCoordinates.chiralEquiv => Physics.SixQuarkConventionalCoordinates.chiralEquiv
assert_compatible GUT.SixQuarkConventionalCoordinates.conventionalEquiv => Physics.SixQuarkConventionalCoordinates.conventionalEquiv
assert_compatible GUT.SixQuarkConventionalCoordinates.conventional_determinant => Physics.SixQuarkConventionalCoordinates.conventional_determinant
assert_compatible GUT.SixQuarkConventionalCoordinates.descend_block => Physics.SixQuarkConventionalCoordinates.descend_block
assert_compatible GUT.SixQuarkConventionalCoordinates.fierz => Physics.SixQuarkConventionalCoordinates.fierz
assert_compatible GUT.SixQuarkConventionalCoordinates.probes_O1 => Physics.SixQuarkConventionalCoordinates.probes_O1
assert_compatible GUT.SixQuarkConventionalCoordinates.probes_O2 => Physics.SixQuarkConventionalCoordinates.probes_O2
assert_compatible GUT.SixQuarkConventionalCoordinates.probes_O3 => Physics.SixQuarkConventionalCoordinates.probes_O3
assert_compatible GUT.SixQuarkConventionalCoordinates.probes_Q1 => Physics.SixQuarkConventionalCoordinates.probes_Q1
assert_compatible GUT.SixQuarkConventionalCoordinates.probes_Q4 => Physics.SixQuarkConventionalCoordinates.probes_Q4
assert_compatible GUT.SixQuarkConventionalCoordinates.reconstruct => Physics.SixQuarkConventionalCoordinates.reconstruct
assert_compatible GUT.SixQuarkConventionalCoordinates.reconstruct_chiral => Physics.SixQuarkConventionalCoordinates.reconstruct_chiral
assert_compatible GUT.SixQuarkSpeciesQuotient.twoProbes.eq_1 => Physics.SixQuarkSpeciesQuotient.twoProbes.eq_1
