import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTypedFlavor
import Physics.StandardModel.Operators.SixQuarkFlavorResidualHom
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTypedFlavor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SixQuarkFlavorCoordinates.IsTypedSwapAlternating.eq_1 => Physics.SixQuarkFlavorCoordinates.IsTypedSwapAlternating.eq_1,
  GUT.SixQuarkFlavorCoordinates.exchangeFlavor.eq_1 => Physics.SixQuarkFlavorCoordinates.exchangeFlavor.eq_1,
  GUT.SixQuarkFlavorResidualHom.residualHom.congr_simp => Physics.SixQuarkFlavorResidualHom.residualHom.congr_simp,
  GUT.SixQuarkTypedFlavor.Coefficients => Physics.SixQuarkTypedFlavor.Coefficients,
  GUT.SixQuarkTypedFlavor.Flavor => Physics.SixQuarkTypedFlavor.Flavor,
  GUT.SixQuarkTypedFlavor.SlotFlavor => Physics.SixQuarkTypedFlavor.SlotFlavor,
  GUT.SixQuarkTypedFlavor.StatisticsHom => Physics.SixQuarkTypedFlavor.StatisticsHom,
  GUT.SixQuarkTypedFlavor.coefficientSubmodule => Physics.SixQuarkTypedFlavor.coefficientSubmodule,
  GUT.SixQuarkTypedFlavor.exists_nonzero_iff => Physics.SixQuarkTypedFlavor.exists_nonzero_iff,
  GUT.SixQuarkTypedFlavor.flavorAddCommGroup => Physics.SixQuarkTypedFlavor.flavorAddCommGroup,
  GUT.SixQuarkTypedFlavor.flavorFiniteDimensional => Physics.SixQuarkTypedFlavor.flavorFiniteDimensional,
  GUT.SixQuarkTypedFlavor.flavorModule => Physics.SixQuarkTypedFlavor.flavorModule,
  GUT.SixQuarkTypedFlavor.flavorRepresentation => Physics.SixQuarkTypedFlavor.flavorRepresentation,
  GUT.SixQuarkTypedFlavor.fromHom => Physics.SixQuarkTypedFlavor.fromHom,
  GUT.SixQuarkTypedFlavor.homEquiv => Physics.SixQuarkTypedFlavor.homEquiv,
  GUT.SixQuarkTypedFlavor.homLinearEquiv => Physics.SixQuarkTypedFlavor.homLinearEquiv,
  GUT.SixQuarkTypedFlavor.homLinearEquiv_apply => Physics.SixQuarkTypedFlavor.homLinearEquiv_apply,
  GUT.SixQuarkTypedFlavor.homLinearEquiv_symm_apply => Physics.SixQuarkTypedFlavor.homLinearEquiv_symm_apply,
  GUT.SixQuarkTypedFlavor.slotRepresentation => Physics.SixQuarkTypedFlavor.slotRepresentation,
  GUT.SixQuarkTypedFlavor.speciesExchange => Physics.SixQuarkTypedFlavor.speciesExchange,
  GUT.SixQuarkTypedFlavor.statisticsSubmodule => Physics.SixQuarkTypedFlavor.statisticsSubmodule,
  GUT.SixQuarkTypedFlavor.statistics_iff => Physics.SixQuarkTypedFlavor.statistics_iff,
  GUT.SixQuarkTypedFlavor.swapCoefficient => Physics.SixQuarkTypedFlavor.swapCoefficient,
  GUT.SixQuarkTypedFlavor.swapCoefficient_apply => Physics.SixQuarkTypedFlavor.swapCoefficient_apply,
  GUT.SixQuarkTypedFlavor.tensorExchange => Physics.SixQuarkTypedFlavor.tensorExchange,
  GUT.SixQuarkTypedFlavor.tensorExchange.eq_1 => Physics.SixQuarkTypedFlavor.tensorExchange.eq_1,
  GUT.SixQuarkTypedFlavor.toHom => Physics.SixQuarkTypedFlavor.toHom,
  GUT.SixQuarkTypedFlavor.typed_swap_full => Physics.SixQuarkTypedFlavor.typed_swap_full
]

assert_compatible GUT.SixQuarkFlavorCoordinates.IsTypedSwapAlternating.eq_1 => Physics.SixQuarkFlavorCoordinates.IsTypedSwapAlternating.eq_1
assert_compatible GUT.SixQuarkFlavorCoordinates.exchangeFlavor.eq_1 => Physics.SixQuarkFlavorCoordinates.exchangeFlavor.eq_1
assert_compatible GUT.SixQuarkFlavorResidualHom.residualHom.congr_simp => Physics.SixQuarkFlavorResidualHom.residualHom.congr_simp
assert_compatible GUT.SixQuarkTypedFlavor.Coefficients => Physics.SixQuarkTypedFlavor.Coefficients
assert_compatible GUT.SixQuarkTypedFlavor.Flavor => Physics.SixQuarkTypedFlavor.Flavor
assert_compatible GUT.SixQuarkTypedFlavor.SlotFlavor => Physics.SixQuarkTypedFlavor.SlotFlavor
assert_compatible GUT.SixQuarkTypedFlavor.StatisticsHom => Physics.SixQuarkTypedFlavor.StatisticsHom
assert_compatible GUT.SixQuarkTypedFlavor.coefficientSubmodule => Physics.SixQuarkTypedFlavor.coefficientSubmodule
assert_compatible GUT.SixQuarkTypedFlavor.exists_nonzero_iff => Physics.SixQuarkTypedFlavor.exists_nonzero_iff
assert_compatible GUT.SixQuarkTypedFlavor.flavorAddCommGroup => Physics.SixQuarkTypedFlavor.flavorAddCommGroup
assert_compatible GUT.SixQuarkTypedFlavor.flavorFiniteDimensional => Physics.SixQuarkTypedFlavor.flavorFiniteDimensional
assert_compatible GUT.SixQuarkTypedFlavor.flavorModule => Physics.SixQuarkTypedFlavor.flavorModule
assert_compatible GUT.SixQuarkTypedFlavor.flavorRepresentation => Physics.SixQuarkTypedFlavor.flavorRepresentation
assert_compatible GUT.SixQuarkTypedFlavor.fromHom => Physics.SixQuarkTypedFlavor.fromHom
assert_compatible GUT.SixQuarkTypedFlavor.homEquiv => Physics.SixQuarkTypedFlavor.homEquiv
assert_compatible GUT.SixQuarkTypedFlavor.homLinearEquiv => Physics.SixQuarkTypedFlavor.homLinearEquiv
assert_compatible GUT.SixQuarkTypedFlavor.homLinearEquiv_apply => Physics.SixQuarkTypedFlavor.homLinearEquiv_apply
assert_compatible GUT.SixQuarkTypedFlavor.homLinearEquiv_symm_apply => Physics.SixQuarkTypedFlavor.homLinearEquiv_symm_apply
assert_compatible GUT.SixQuarkTypedFlavor.slotRepresentation => Physics.SixQuarkTypedFlavor.slotRepresentation
assert_compatible GUT.SixQuarkTypedFlavor.speciesExchange => Physics.SixQuarkTypedFlavor.speciesExchange
assert_compatible GUT.SixQuarkTypedFlavor.statisticsSubmodule => Physics.SixQuarkTypedFlavor.statisticsSubmodule
assert_compatible GUT.SixQuarkTypedFlavor.statistics_iff => Physics.SixQuarkTypedFlavor.statistics_iff
assert_compatible GUT.SixQuarkTypedFlavor.swapCoefficient => Physics.SixQuarkTypedFlavor.swapCoefficient
assert_compatible GUT.SixQuarkTypedFlavor.swapCoefficient_apply => Physics.SixQuarkTypedFlavor.swapCoefficient_apply
assert_compatible GUT.SixQuarkTypedFlavor.tensorExchange => Physics.SixQuarkTypedFlavor.tensorExchange
assert_compatible GUT.SixQuarkTypedFlavor.tensorExchange.eq_1 => Physics.SixQuarkTypedFlavor.tensorExchange.eq_1
assert_compatible GUT.SixQuarkTypedFlavor.toHom => Physics.SixQuarkTypedFlavor.toHom
assert_compatible GUT.SixQuarkTypedFlavor.typed_swap_full => Physics.SixQuarkTypedFlavor.typed_swap_full
