import Physics.StandardModel.Spectrum.Representations.InverseCyclicSMRealization
import Physics.StandardModel.Operators.InverseLeptonParitySelection
import Physics.StandardModel.Operators.InverseCyclicSMCharges
import Physics.FieldTheory.Mass.ConstructedSpectatorRadical
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.InverseCyclicSMRealization instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InvariantWeylMass.ofDirac.eq_1 => Physics.InvariantWeylMass.ofDirac.eq_1,
  GUT.InverseCyclicSMRealization.Carrier => Physics.InverseCyclicSMRealization.Carrier,
  GUT.InverseCyclicSMRealization.Flavor => Physics.InverseCyclicSMRealization.Flavor,
  GUT.InverseCyclicSMRealization.G => Physics.InverseCyclicSMRealization.G,
  GUT.InverseCyclicSMRealization.H => Physics.InverseCyclicSMRealization.H,
  GUT.InverseCyclicSMRealization.Light => Physics.InverseCyclicSMRealization.Light,
  GUT.InverseCyclicSMRealization.all_B1_forbidden => Physics.InverseCyclicSMRealization.all_B1_forbidden,
  GUT.InverseCyclicSMRealization.chiral_left => Physics.InverseCyclicSMRealization.chiral_left,
  GUT.InverseCyclicSMRealization.coefficientGroup => Physics.InverseCyclicSMRealization.coefficientGroup,
  GUT.InverseCyclicSMRealization.coefficientGroup.eq_1 => Physics.InverseCyclicSMRealization.coefficientGroup.eq_1,
  GUT.InverseCyclicSMRealization.coefficient_species => Physics.InverseCyclicSMRealization.coefficient_species,
  GUT.InverseCyclicSMRealization.fermionFlavor => Physics.InverseCyclicSMRealization.fermionFlavor,
  GUT.InverseCyclicSMRealization.flavorDualEquiv => Physics.InverseCyclicSMRealization.flavorDualEquiv,
  GUT.InverseCyclicSMRealization.flavorDual_action => Physics.InverseCyclicSMRealization.flavorDual_action,
  GUT.InverseCyclicSMRealization.gaugeSpecies => Physics.InverseCyclicSMRealization.gaugeSpecies,
  GUT.InverseCyclicSMRealization.gaugeSpecies.eq_1 => Physics.InverseCyclicSMRealization.gaugeSpecies.eq_1,
  GUT.InverseCyclicSMRealization.gauge_restriction => Physics.InverseCyclicSMRealization.gauge_restriction,
  GUT.InverseCyclicSMRealization.higgsFlavor => Physics.InverseCyclicSMRealization.higgsFlavor,
  GUT.InverseCyclicSMRealization.higgs_residual_neutral => Physics.InverseCyclicSMRealization.higgs_residual_neutral,
  GUT.InverseCyclicSMRealization.index => Physics.InverseCyclicSMRealization.index,
  GUT.InverseCyclicSMRealization.instAddCommGroupCarrier => Physics.InverseCyclicSMRealization.instAddCommGroupCarrier,
  GUT.InverseCyclicSMRealization.instModuleComplexCarrier => Physics.InverseCyclicSMRealization.instModuleComplexCarrier,
  GUT.InverseCyclicSMRealization.light => Physics.InverseCyclicSMRealization.light,
  GUT.InverseCyclicSMRealization.mass => Physics.InverseCyclicSMRealization.mass,
  GUT.InverseCyclicSMRealization.mass.eq_1 => Physics.InverseCyclicSMRealization.mass.eq_1,
  GUT.InverseCyclicSMRealization.original => Physics.InverseCyclicSMRealization.original,
  GUT.InverseCyclicSMRealization.physicalFieldEquiv => Physics.InverseCyclicSMRealization.physicalFieldEquiv,
  GUT.InverseCyclicSMRealization.radicalEquiv => Physics.InverseCyclicSMRealization.radicalEquiv,
  GUT.InverseCyclicSMRealization.selected_dictionary => Physics.InverseCyclicSMRealization.selected_dictionary,
  GUT.InverseCyclicSMRealization.sm => Physics.InverseCyclicSMRealization.sm,
  GUT.InverseCyclicSMRealization.species => Physics.InverseCyclicSMRealization.species,
  GUT.InverseCyclicSMRealization.species.eq_1 => Physics.InverseCyclicSMRealization.species.eq_1,
  GUT.InverseCyclicSMRealization.species_gauge => Physics.InverseCyclicSMRealization.species_gauge,
  GUT.InverseCyclicSMRealization.spectator => Physics.InverseCyclicSMRealization.spectator,
  GUT.InverseCyclicSMRealization.spectator_mass_nonzero => Physics.InverseCyclicSMRealization.spectator_mass_nonzero,
  GUT.InverseCyclicSMRealization.threeCopies => Physics.InverseCyclicSMRealization.threeCopies,
  GUT.LightInheritanceBoundary.pairedMass.eq_1 => Physics.LightInheritanceBoundary.pairedMass.eq_1
]

assert_compatible GUT.InvariantWeylMass.ofDirac.eq_1 => Physics.InvariantWeylMass.ofDirac.eq_1
assert_compatible GUT.InverseCyclicSMRealization.Carrier => Physics.InverseCyclicSMRealization.Carrier
assert_compatible GUT.InverseCyclicSMRealization.Flavor => Physics.InverseCyclicSMRealization.Flavor
assert_compatible GUT.InverseCyclicSMRealization.G => Physics.InverseCyclicSMRealization.G
assert_compatible GUT.InverseCyclicSMRealization.H => Physics.InverseCyclicSMRealization.H
assert_compatible GUT.InverseCyclicSMRealization.Light => Physics.InverseCyclicSMRealization.Light
assert_compatible GUT.InverseCyclicSMRealization.all_B1_forbidden => Physics.InverseCyclicSMRealization.all_B1_forbidden
assert_compatible GUT.InverseCyclicSMRealization.chiral_left => Physics.InverseCyclicSMRealization.chiral_left
assert_compatible GUT.InverseCyclicSMRealization.coefficientGroup => Physics.InverseCyclicSMRealization.coefficientGroup
assert_compatible GUT.InverseCyclicSMRealization.coefficientGroup.eq_1 => Physics.InverseCyclicSMRealization.coefficientGroup.eq_1
assert_compatible GUT.InverseCyclicSMRealization.coefficient_species => Physics.InverseCyclicSMRealization.coefficient_species
assert_compatible GUT.InverseCyclicSMRealization.fermionFlavor => Physics.InverseCyclicSMRealization.fermionFlavor
assert_compatible GUT.InverseCyclicSMRealization.flavorDualEquiv => Physics.InverseCyclicSMRealization.flavorDualEquiv
assert_compatible GUT.InverseCyclicSMRealization.flavorDual_action => Physics.InverseCyclicSMRealization.flavorDual_action
assert_compatible GUT.InverseCyclicSMRealization.gaugeSpecies => Physics.InverseCyclicSMRealization.gaugeSpecies
assert_compatible GUT.InverseCyclicSMRealization.gaugeSpecies.eq_1 => Physics.InverseCyclicSMRealization.gaugeSpecies.eq_1
assert_compatible GUT.InverseCyclicSMRealization.gauge_restriction => Physics.InverseCyclicSMRealization.gauge_restriction
assert_compatible GUT.InverseCyclicSMRealization.higgsFlavor => Physics.InverseCyclicSMRealization.higgsFlavor
assert_compatible GUT.InverseCyclicSMRealization.higgs_residual_neutral => Physics.InverseCyclicSMRealization.higgs_residual_neutral
assert_compatible GUT.InverseCyclicSMRealization.index => Physics.InverseCyclicSMRealization.index
assert_compatible GUT.InverseCyclicSMRealization.instAddCommGroupCarrier => Physics.InverseCyclicSMRealization.instAddCommGroupCarrier
assert_compatible GUT.InverseCyclicSMRealization.instModuleComplexCarrier => Physics.InverseCyclicSMRealization.instModuleComplexCarrier
assert_compatible GUT.InverseCyclicSMRealization.light => Physics.InverseCyclicSMRealization.light
assert_compatible GUT.InverseCyclicSMRealization.mass => Physics.InverseCyclicSMRealization.mass
assert_compatible GUT.InverseCyclicSMRealization.mass.eq_1 => Physics.InverseCyclicSMRealization.mass.eq_1
assert_compatible GUT.InverseCyclicSMRealization.original => Physics.InverseCyclicSMRealization.original
assert_compatible GUT.InverseCyclicSMRealization.physicalFieldEquiv => Physics.InverseCyclicSMRealization.physicalFieldEquiv
assert_compatible GUT.InverseCyclicSMRealization.radicalEquiv => Physics.InverseCyclicSMRealization.radicalEquiv
assert_compatible GUT.InverseCyclicSMRealization.selected_dictionary => Physics.InverseCyclicSMRealization.selected_dictionary
assert_compatible GUT.InverseCyclicSMRealization.sm => Physics.InverseCyclicSMRealization.sm
assert_compatible GUT.InverseCyclicSMRealization.species => Physics.InverseCyclicSMRealization.species
assert_compatible GUT.InverseCyclicSMRealization.species.eq_1 => Physics.InverseCyclicSMRealization.species.eq_1
assert_compatible GUT.InverseCyclicSMRealization.species_gauge => Physics.InverseCyclicSMRealization.species_gauge
assert_compatible GUT.InverseCyclicSMRealization.spectator => Physics.InverseCyclicSMRealization.spectator
assert_compatible GUT.InverseCyclicSMRealization.spectator_mass_nonzero => Physics.InverseCyclicSMRealization.spectator_mass_nonzero
assert_compatible GUT.InverseCyclicSMRealization.threeCopies => Physics.InverseCyclicSMRealization.threeCopies
assert_compatible GUT.LightInheritanceBoundary.pairedMass.eq_1 => Physics.LightInheritanceBoundary.pairedMass.eq_1
