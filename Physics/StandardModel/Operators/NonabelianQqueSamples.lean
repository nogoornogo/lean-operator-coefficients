import Physics.StandardModel.Operators.BaryonOne.Qque.NonabelianQqueSamples
import Physics.StandardModel.Operators.S3DipoleSelection
import Physics.StandardModel.Operators.QqueSpinorExterior
import Math.RepresentationTheory.FiniteFlavorControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.NonabelianQqueSamples instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.NonabelianQqueSamples.a4_action_noncommuting => Physics.NonabelianQqueSamples.a4_action_noncommuting,
  GUT.NonabelianQqueSamples.a4_left_species_allowed => Physics.NonabelianQqueSamples.a4_left_species_allowed,
  GUT.NonabelianQqueSamples.a4_no_single_invariant_but_qque => Physics.NonabelianQqueSamples.a4_no_single_invariant_but_qque,
  GUT.NonabelianQqueSamples.a4_qque_allowed => Physics.NonabelianQqueSamples.a4_qque_allowed,
  GUT.NonabelianQqueSamples.common_flavor_left_species => Physics.NonabelianQqueSamples.common_flavor_left_species,
  GUT.NonabelianQqueSamples.instAddCommGroupQuark => Physics.NonabelianQqueSamples.instAddCommGroupQuark,
  GUT.NonabelianQqueSamples.s3_action_noncommuting => Physics.NonabelianQqueSamples.s3_action_noncommuting,
  GUT.NonabelianQqueSamples.s3_left_species_allowed => Physics.NonabelianQqueSamples.s3_left_species_allowed,
  GUT.NonabelianQqueSamples.s3_qque_allowed => Physics.NonabelianQqueSamples.s3_qque_allowed
]

assert_compatible GUT.NonabelianQqueSamples.a4_action_noncommuting => Physics.NonabelianQqueSamples.a4_action_noncommuting
assert_compatible GUT.NonabelianQqueSamples.a4_left_species_allowed => Physics.NonabelianQqueSamples.a4_left_species_allowed
assert_compatible GUT.NonabelianQqueSamples.a4_no_single_invariant_but_qque => Physics.NonabelianQqueSamples.a4_no_single_invariant_but_qque
assert_compatible GUT.NonabelianQqueSamples.a4_qque_allowed => Physics.NonabelianQqueSamples.a4_qque_allowed
assert_compatible GUT.NonabelianQqueSamples.common_flavor_left_species => Physics.NonabelianQqueSamples.common_flavor_left_species
assert_compatible GUT.NonabelianQqueSamples.instAddCommGroupQuark => Physics.NonabelianQqueSamples.instAddCommGroupQuark
assert_compatible GUT.NonabelianQqueSamples.s3_action_noncommuting => Physics.NonabelianQqueSamples.s3_action_noncommuting
assert_compatible GUT.NonabelianQqueSamples.s3_left_species_allowed => Physics.NonabelianQqueSamples.s3_left_species_allowed
assert_compatible GUT.NonabelianQqueSamples.s3_qque_allowed => Physics.NonabelianQqueSamples.s3_qque_allowed
