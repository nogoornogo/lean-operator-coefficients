import Physics.StandardModel.Spectrum.Representations.ExactSMSpectrum
import Physics.StandardModel.Gauge.StandardSMIrreducibility
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.ExactSMSpectrum instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExactSMSpectrum.Generation => Physics.ExactSMSpectrum.Generation,
  GUT.ExactSMSpectrum.HasHypercharge => Physics.ExactSMSpectrum.HasHypercharge,
  GUT.ExactSMSpectrum.HasSpectrum => Physics.ExactSMSpectrum.HasSpectrum,
  GUT.ExactSMSpectrum.Space => Physics.ExactSMSpectrum.Space,
  GUT.ExactSMSpectrum.action => Physics.ExactSMSpectrum.action,
  GUT.ExactSMSpectrum.action.eq_1 => Physics.ExactSMSpectrum.action.eq_1,
  GUT.ExactSMSpectrum.downLeft_hypercharge => Physics.ExactSMSpectrum.downLeft_hypercharge,
  GUT.ExactSMSpectrum.downRight_hypercharge => Physics.ExactSMSpectrum.downRight_hypercharge,
  GUT.ExactSMSpectrum.electronLeft_hypercharge => Physics.ExactSMSpectrum.electronLeft_hypercharge,
  GUT.ExactSMSpectrum.electronRight_hypercharge => Physics.ExactSMSpectrum.electronRight_hypercharge,
  GUT.ExactSMSpectrum.electron_generation => Physics.ExactSMSpectrum.electron_generation,
  GUT.ExactSMSpectrum.exact_opposite_multiplicities => Physics.ExactSMSpectrum.exact_opposite_multiplicities,
  GUT.ExactSMSpectrum.exact_species_multiplicities => Physics.ExactSMSpectrum.exact_species_multiplicities,
  GUT.ExactSMSpectrum.generation => Physics.ExactSMSpectrum.generation,
  GUT.ExactSMSpectrum.hom_action => Physics.ExactSMSpectrum.hom_action,
  GUT.ExactSMSpectrum.hom_exact => Physics.ExactSMSpectrum.hom_exact,
  GUT.ExactSMSpectrum.hom_finrank_zero_of_hypercharge_ne => Physics.ExactSMSpectrum.hom_finrank_zero_of_hypercharge_ne,
  GUT.ExactSMSpectrum.hom_generation_zero => Physics.ExactSMSpectrum.hom_generation_zero,
  GUT.ExactSMSpectrum.hypercharge_dual => Physics.ExactSMSpectrum.hypercharge_dual,
  GUT.ExactSMSpectrum.intertwiner_eq_zero_of_hypercharge_ne => Physics.ExactSMSpectrum.intertwiner_eq_zero_of_hypercharge_ne,
  GUT.ExactSMSpectrum.lepton_hypercharge => Physics.ExactSMSpectrum.lepton_hypercharge,
  GUT.ExactSMSpectrum.quark_generation => Physics.ExactSMSpectrum.quark_generation,
  GUT.ExactSMSpectrum.quark_hypercharge => Physics.ExactSMSpectrum.quark_hypercharge,
  GUT.ExactSMSpectrum.trivial_hypercharge => Physics.ExactSMSpectrum.trivial_hypercharge,
  GUT.ExactSMSpectrum.upLeft_hypercharge => Physics.ExactSMSpectrum.upLeft_hypercharge,
  GUT.ExactSMSpectrum.upRight_hypercharge => Physics.ExactSMSpectrum.upRight_hypercharge,
  GUT.ExactSMSpectrum.up_generation => Physics.ExactSMSpectrum.up_generation
]

assert_compatible GUT.ExactSMSpectrum.Generation => Physics.ExactSMSpectrum.Generation
assert_compatible GUT.ExactSMSpectrum.HasHypercharge => Physics.ExactSMSpectrum.HasHypercharge
assert_compatible GUT.ExactSMSpectrum.HasSpectrum => Physics.ExactSMSpectrum.HasSpectrum
assert_compatible GUT.ExactSMSpectrum.Space => Physics.ExactSMSpectrum.Space
assert_compatible GUT.ExactSMSpectrum.action => Physics.ExactSMSpectrum.action
assert_compatible GUT.ExactSMSpectrum.action.eq_1 => Physics.ExactSMSpectrum.action.eq_1
assert_compatible GUT.ExactSMSpectrum.downLeft_hypercharge => Physics.ExactSMSpectrum.downLeft_hypercharge
assert_compatible GUT.ExactSMSpectrum.downRight_hypercharge => Physics.ExactSMSpectrum.downRight_hypercharge
assert_compatible GUT.ExactSMSpectrum.electronLeft_hypercharge => Physics.ExactSMSpectrum.electronLeft_hypercharge
assert_compatible GUT.ExactSMSpectrum.electronRight_hypercharge => Physics.ExactSMSpectrum.electronRight_hypercharge
assert_compatible GUT.ExactSMSpectrum.electron_generation => Physics.ExactSMSpectrum.electron_generation
assert_compatible GUT.ExactSMSpectrum.exact_opposite_multiplicities => Physics.ExactSMSpectrum.exact_opposite_multiplicities
assert_compatible GUT.ExactSMSpectrum.exact_species_multiplicities => Physics.ExactSMSpectrum.exact_species_multiplicities
assert_compatible GUT.ExactSMSpectrum.generation => Physics.ExactSMSpectrum.generation
assert_compatible GUT.ExactSMSpectrum.hom_action => Physics.ExactSMSpectrum.hom_action
assert_compatible GUT.ExactSMSpectrum.hom_exact => Physics.ExactSMSpectrum.hom_exact
assert_compatible GUT.ExactSMSpectrum.hom_finrank_zero_of_hypercharge_ne => Physics.ExactSMSpectrum.hom_finrank_zero_of_hypercharge_ne
assert_compatible GUT.ExactSMSpectrum.hom_generation_zero => Physics.ExactSMSpectrum.hom_generation_zero
assert_compatible GUT.ExactSMSpectrum.hypercharge_dual => Physics.ExactSMSpectrum.hypercharge_dual
assert_compatible GUT.ExactSMSpectrum.intertwiner_eq_zero_of_hypercharge_ne => Physics.ExactSMSpectrum.intertwiner_eq_zero_of_hypercharge_ne
assert_compatible GUT.ExactSMSpectrum.lepton_hypercharge => Physics.ExactSMSpectrum.lepton_hypercharge
assert_compatible GUT.ExactSMSpectrum.quark_generation => Physics.ExactSMSpectrum.quark_generation
assert_compatible GUT.ExactSMSpectrum.quark_hypercharge => Physics.ExactSMSpectrum.quark_hypercharge
assert_compatible GUT.ExactSMSpectrum.trivial_hypercharge => Physics.ExactSMSpectrum.trivial_hypercharge
assert_compatible GUT.ExactSMSpectrum.upLeft_hypercharge => Physics.ExactSMSpectrum.upLeft_hypercharge
assert_compatible GUT.ExactSMSpectrum.upRight_hypercharge => Physics.ExactSMSpectrum.upRight_hypercharge
assert_compatible GUT.ExactSMSpectrum.up_generation => Physics.ExactSMSpectrum.up_generation
