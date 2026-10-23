import Physics.StandardModel.Operators.Selection.InverseCyclicChargeOrbits
import Math.RepresentationTheory.CyclicChargeOrbits
import Physics.StandardModel.Operators.InverseCyclicSMCharges
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.InverseCyclicChargeOrbits instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InverseCyclicChargeOrbits.effectiveCount => Physics.InverseCyclicChargeOrbits.effectiveCount,
  GUT.InverseCyclicChargeOrbits.effective_counts => Physics.InverseCyclicChargeOrbits.effective_counts,
  GUT.InverseCyclicChargeOrbits.orbitClasses => Physics.InverseCyclicChargeOrbits.orbitClasses,
  GUT.InverseCyclicChargeOrbits.orbit_counts => Physics.InverseCyclicChargeOrbits.orbit_counts,
  GUT.InverseCyclicChargeOrbits.preserves_b2 => Physics.InverseCyclicChargeOrbits.preserves_b2,
  GUT.InverseCyclicChargeOrbits.preserves_bnv => Physics.InverseCyclicChargeOrbits.preserves_bnv,
  GUT.InverseCyclicChargeOrbits.preserves_llhh => Physics.InverseCyclicChargeOrbits.preserves_llhh,
  GUT.InverseCyclicChargeOrbits.total_orbits => Physics.InverseCyclicChargeOrbits.total_orbits
]

assert_compatible GUT.InverseCyclicChargeOrbits.effectiveCount => Physics.InverseCyclicChargeOrbits.effectiveCount
assert_compatible GUT.InverseCyclicChargeOrbits.effective_counts => Physics.InverseCyclicChargeOrbits.effective_counts
assert_compatible GUT.InverseCyclicChargeOrbits.orbitClasses => Physics.InverseCyclicChargeOrbits.orbitClasses
assert_compatible GUT.InverseCyclicChargeOrbits.orbit_counts => Physics.InverseCyclicChargeOrbits.orbit_counts
assert_compatible GUT.InverseCyclicChargeOrbits.preserves_b2 => Physics.InverseCyclicChargeOrbits.preserves_b2
assert_compatible GUT.InverseCyclicChargeOrbits.preserves_bnv => Physics.InverseCyclicChargeOrbits.preserves_bnv
assert_compatible GUT.InverseCyclicChargeOrbits.preserves_llhh => Physics.InverseCyclicChargeOrbits.preserves_llhh
assert_compatible GUT.InverseCyclicChargeOrbits.total_orbits => Physics.InverseCyclicChargeOrbits.total_orbits
