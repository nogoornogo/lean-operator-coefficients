import Physics.FieldTheory.Jets.Gauge.YangMillsFirstVariation
import Math.Algebra.JetFirstVariation
import Math.Algebra.ConnectionFirstVariation
import Physics.FieldTheory.Jets.YangMillsGaugeTrace
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Gauge.YangMillsFirstVariation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FormalYangMills.F.eq_1 => Physics.FormalYangMills.F.eq_1,
  GUT.FormalYangMills.nabla.eq_1 => Physics.FormalYangMills.nabla.eq_1,
  GUT.YangMillsFirstVariation.componentVariation => Physics.YangMillsFirstVariation.componentVariation,
  GUT.YangMillsFirstVariation.componentVariation.eq_1 => Physics.YangMillsFirstVariation.componentVariation.eq_1,
  GUT.YangMillsFirstVariation.component_eom_iff => Physics.YangMillsFirstVariation.component_eom_iff,
  GUT.YangMillsFirstVariation.component_first_variation_mod_ibp => Physics.YangMillsFirstVariation.component_first_variation_mod_ibp,
  GUT.YangMillsFirstVariation.component_pairing => Physics.YangMillsFirstVariation.component_pairing,
  GUT.YangMillsFirstVariation.current => Physics.YangMillsFirstVariation.current,
  GUT.YangMillsFirstVariation.current.eq_1 => Physics.YangMillsFirstVariation.current.eq_1,
  GUT.YangMillsFirstVariation.curvature_variation => Physics.YangMillsFirstVariation.curvature_variation,
  GUT.YangMillsFirstVariation.delta => Physics.YangMillsFirstVariation.delta,
  GUT.YangMillsFirstVariation.delta_connection => Physics.YangMillsFirstVariation.delta_connection,
  GUT.YangMillsFirstVariation.delta_derivative => Physics.YangMillsFirstVariation.delta_derivative,
  GUT.YangMillsFirstVariation.eomPairing => Physics.YangMillsFirstVariation.eomPairing,
  GUT.YangMillsFirstVariation.eomPairing.eq_1 => Physics.YangMillsFirstVariation.eomPairing.eq_1,
  GUT.YangMillsFirstVariation.eomPairing_mem => Physics.YangMillsFirstVariation.eomPairing_mem,
  GUT.YangMillsFirstVariation.eulerSeeds => Physics.YangMillsFirstVariation.eulerSeeds,
  GUT.YangMillsFirstVariation.euler_ideal_eq => Physics.YangMillsFirstVariation.euler_ideal_eq,
  GUT.YangMillsFirstVariation.first_variation => Physics.YangMillsFirstVariation.first_variation,
  GUT.YangMillsFirstVariation.first_variation_mod_ibp => Physics.YangMillsFirstVariation.first_variation_mod_ibp,
  GUT.YangMillsFirstVariation.first_variation_onShell => Physics.YangMillsFirstVariation.first_variation_onShell,
  GUT.YangMillsFirstVariation.lagrangian => Physics.YangMillsFirstVariation.lagrangian,
  GUT.YangMillsFirstVariation.lagrangian.eq_1 => Physics.YangMillsFirstVariation.lagrangian.eq_1,
  GUT.YangMillsFirstVariation.matrixDelta => Physics.YangMillsFirstVariation.matrixDelta,
  GUT.YangMillsFirstVariation.ordinary_bridge => Physics.YangMillsFirstVariation.ordinary_bridge,
  GUT.YangMillsFirstVariation.substitution_first => Physics.YangMillsFirstVariation.substitution_first
]

assert_compatible GUT.FormalYangMills.F.eq_1 => Physics.FormalYangMills.F.eq_1
assert_compatible GUT.FormalYangMills.nabla.eq_1 => Physics.FormalYangMills.nabla.eq_1
assert_compatible GUT.YangMillsFirstVariation.componentVariation => Physics.YangMillsFirstVariation.componentVariation
assert_compatible GUT.YangMillsFirstVariation.componentVariation.eq_1 => Physics.YangMillsFirstVariation.componentVariation.eq_1
assert_compatible GUT.YangMillsFirstVariation.component_eom_iff => Physics.YangMillsFirstVariation.component_eom_iff
assert_compatible GUT.YangMillsFirstVariation.component_first_variation_mod_ibp => Physics.YangMillsFirstVariation.component_first_variation_mod_ibp
assert_compatible GUT.YangMillsFirstVariation.component_pairing => Physics.YangMillsFirstVariation.component_pairing
assert_compatible GUT.YangMillsFirstVariation.current => Physics.YangMillsFirstVariation.current
assert_compatible GUT.YangMillsFirstVariation.current.eq_1 => Physics.YangMillsFirstVariation.current.eq_1
assert_compatible GUT.YangMillsFirstVariation.curvature_variation => Physics.YangMillsFirstVariation.curvature_variation
assert_compatible GUT.YangMillsFirstVariation.delta => Physics.YangMillsFirstVariation.delta
assert_compatible GUT.YangMillsFirstVariation.delta_connection => Physics.YangMillsFirstVariation.delta_connection
assert_compatible GUT.YangMillsFirstVariation.delta_derivative => Physics.YangMillsFirstVariation.delta_derivative
assert_compatible GUT.YangMillsFirstVariation.eomPairing => Physics.YangMillsFirstVariation.eomPairing
assert_compatible GUT.YangMillsFirstVariation.eomPairing.eq_1 => Physics.YangMillsFirstVariation.eomPairing.eq_1
assert_compatible GUT.YangMillsFirstVariation.eomPairing_mem => Physics.YangMillsFirstVariation.eomPairing_mem
assert_compatible GUT.YangMillsFirstVariation.eulerSeeds => Physics.YangMillsFirstVariation.eulerSeeds
assert_compatible GUT.YangMillsFirstVariation.euler_ideal_eq => Physics.YangMillsFirstVariation.euler_ideal_eq
assert_compatible GUT.YangMillsFirstVariation.first_variation => Physics.YangMillsFirstVariation.first_variation
assert_compatible GUT.YangMillsFirstVariation.first_variation_mod_ibp => Physics.YangMillsFirstVariation.first_variation_mod_ibp
assert_compatible GUT.YangMillsFirstVariation.first_variation_onShell => Physics.YangMillsFirstVariation.first_variation_onShell
assert_compatible GUT.YangMillsFirstVariation.lagrangian => Physics.YangMillsFirstVariation.lagrangian
assert_compatible GUT.YangMillsFirstVariation.lagrangian.eq_1 => Physics.YangMillsFirstVariation.lagrangian.eq_1
assert_compatible GUT.YangMillsFirstVariation.matrixDelta => Physics.YangMillsFirstVariation.matrixDelta
assert_compatible GUT.YangMillsFirstVariation.ordinary_bridge => Physics.YangMillsFirstVariation.ordinary_bridge
assert_compatible GUT.YangMillsFirstVariation.substitution_first => Physics.YangMillsFirstVariation.substitution_first
