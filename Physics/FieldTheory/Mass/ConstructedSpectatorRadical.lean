import Physics.FieldTheory.Mass.Surplus.ConstructedSpectatorRadical
import Physics.FieldTheory.Mass.OrthogonalMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.ConstructedSpectatorRadical instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ConstructedSpectatorRadical.action => Physics.ConstructedSpectatorRadical.action,
  GUT.ConstructedSpectatorRadical.mass => Physics.ConstructedSpectatorRadical.mass,
  GUT.ConstructedSpectatorRadical.mass.eq_1 => Physics.ConstructedSpectatorRadical.mass.eq_1,
  GUT.ConstructedSpectatorRadical.mem_radical => Physics.ConstructedSpectatorRadical.mem_radical,
  GUT.ConstructedSpectatorRadical.radicalEquiv => Physics.ConstructedSpectatorRadical.radicalEquiv
]

assert_compatible GUT.ConstructedSpectatorRadical.action => Physics.ConstructedSpectatorRadical.action
assert_compatible GUT.ConstructedSpectatorRadical.mass => Physics.ConstructedSpectatorRadical.mass
assert_compatible GUT.ConstructedSpectatorRadical.mass.eq_1 => Physics.ConstructedSpectatorRadical.mass.eq_1
assert_compatible GUT.ConstructedSpectatorRadical.mem_radical => Physics.ConstructedSpectatorRadical.mem_radical
assert_compatible GUT.ConstructedSpectatorRadical.radicalEquiv => Physics.ConstructedSpectatorRadical.radicalEquiv
