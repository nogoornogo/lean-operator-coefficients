import Physics.StandardModel.Spectrum.Representations.GaugeTorusTrace
import Physics.StandardModel.Gauge.PhysicalTorus
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.GaugeTorusTrace instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SU5.TorusMatterCharacter.character_prod => Physics.SU5.TorusMatterCharacter.character_prod,
  GUT.SU5.TorusMatterCharacter.character_twist => Physics.SU5.TorusMatterCharacter.character_twist,
  GUT.SU5.TorusMatterCharacter.color_character => Physics.SU5.TorusMatterCharacter.color_character,
  GUT.SU5.TorusMatterCharacter.color_character_inv => Physics.SU5.TorusMatterCharacter.color_character_inv,
  GUT.SU5.TorusMatterCharacter.weak_character => Physics.SU5.TorusMatterCharacter.weak_character,
  GUT.SU5.TorusMatterCharacter.weak_character_inv => Physics.SU5.TorusMatterCharacter.weak_character_inv
]

assert_compatible GUT.SU5.TorusMatterCharacter.character_prod => Physics.SU5.TorusMatterCharacter.character_prod
assert_compatible GUT.SU5.TorusMatterCharacter.character_twist => Physics.SU5.TorusMatterCharacter.character_twist
assert_compatible GUT.SU5.TorusMatterCharacter.color_character => Physics.SU5.TorusMatterCharacter.color_character
assert_compatible GUT.SU5.TorusMatterCharacter.color_character_inv => Physics.SU5.TorusMatterCharacter.color_character_inv
assert_compatible GUT.SU5.TorusMatterCharacter.weak_character => Physics.SU5.TorusMatterCharacter.weak_character
assert_compatible GUT.SU5.TorusMatterCharacter.weak_character_inv => Physics.SU5.TorusMatterCharacter.weak_character_inv
