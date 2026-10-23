import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkResidual
import Physics.StandardModel.Operators.LiSixQuarkLocalBasis
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.DeltaBTwoFlavorOneGeneration
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkResidual instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv.eq_1 => Physics.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv.eq_1,
  GUT.LiSixQuarkLocalBasis.orbitInvariant.eq_1 => Physics.LiSixQuarkLocalBasis.orbitInvariant.eq_1,
  GUT.LiSixQuarkResidual.OrbitHom => Physics.LiSixQuarkResidual.OrbitHom,
  GUT.LiSixQuarkResidual.StatisticsHom => Physics.LiSixQuarkResidual.StatisticsHom,
  GUT.LiSixQuarkResidual.assembleHom => Physics.LiSixQuarkResidual.assembleHom,
  GUT.LiSixQuarkResidual.coefficientEquiv => Physics.LiSixQuarkResidual.coefficientEquiv,
  GUT.LiSixQuarkResidual.extractHom => Physics.LiSixQuarkResidual.extractHom,
  GUT.LiSixQuarkResidual.homEquiv => Physics.LiSixQuarkResidual.homEquiv,
  GUT.LiSixQuarkResidual.literal_local_assembly => Physics.LiSixQuarkResidual.literal_local_assembly,
  GUT.LiSixQuarkResidual.onFieldsEquiv => Physics.LiSixQuarkResidual.onFieldsEquiv,
  GUT.LiSixQuarkResidual.onFields_reconstruction => Physics.LiSixQuarkResidual.onFields_reconstruction,
  GUT.LiSixQuarkResidual.physicalEquiv => Physics.LiSixQuarkResidual.physicalEquiv,
  GUT.LiSixQuarkResidual.physicalEquiv.eq_1 => Physics.LiSixQuarkResidual.physicalEquiv.eq_1,
  GUT.LiSixQuarkResidual.physical_assembly_extraction => Physics.LiSixQuarkResidual.physical_assembly_extraction,
  GUT.LiSixQuarkResidual.physical_extraction_assembly => Physics.LiSixQuarkResidual.physical_extraction_assembly,
  GUT.LiSixQuarkResidual.scalar => Physics.LiSixQuarkResidual.scalar,
  GUT.LiSixQuarkResidual.scalarProbeEquiv => Physics.LiSixQuarkResidual.scalarProbeEquiv,
  GUT.LiSixQuarkResidual.scalarProbeEquiv.eq_1 => Physics.LiSixQuarkResidual.scalarProbeEquiv.eq_1,
  GUT.LiSixQuarkResidual.scalar_finrank => Physics.LiSixQuarkResidual.scalar_finrank,
  GUT.LiSixQuarkResidual.scalar_physical_agrees => Physics.LiSixQuarkResidual.scalar_physical_agrees,
  GUT.LiSixQuarkResidual.slots => Physics.LiSixQuarkResidual.slots,
  GUT.LiSixQuarkResidual.statisticsEquiv => Physics.LiSixQuarkResidual.statisticsEquiv,
  GUT.LiSixQuarkResidual.statisticsSubmodule => Physics.LiSixQuarkResidual.statisticsSubmodule,
  GUT.LiSixQuarkResidual.statistics_iff => Physics.LiSixQuarkResidual.statistics_iff,
  GUT.SixQuarkPermutationCompleteness.coordinatesEquiv.eq_1 => Physics.SixQuarkPermutationCompleteness.coordinatesEquiv.eq_1
]

assert_compatible GUT.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv.eq_1 => Physics.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv.eq_1
assert_compatible GUT.LiSixQuarkLocalBasis.orbitInvariant.eq_1 => Physics.LiSixQuarkLocalBasis.orbitInvariant.eq_1
assert_compatible GUT.LiSixQuarkResidual.OrbitHom => Physics.LiSixQuarkResidual.OrbitHom
assert_compatible GUT.LiSixQuarkResidual.StatisticsHom => Physics.LiSixQuarkResidual.StatisticsHom
assert_compatible GUT.LiSixQuarkResidual.assembleHom => Physics.LiSixQuarkResidual.assembleHom
assert_compatible GUT.LiSixQuarkResidual.coefficientEquiv => Physics.LiSixQuarkResidual.coefficientEquiv
assert_compatible GUT.LiSixQuarkResidual.extractHom => Physics.LiSixQuarkResidual.extractHom
assert_compatible GUT.LiSixQuarkResidual.homEquiv => Physics.LiSixQuarkResidual.homEquiv
assert_compatible GUT.LiSixQuarkResidual.literal_local_assembly => Physics.LiSixQuarkResidual.literal_local_assembly
assert_compatible GUT.LiSixQuarkResidual.onFieldsEquiv => Physics.LiSixQuarkResidual.onFieldsEquiv
assert_compatible GUT.LiSixQuarkResidual.onFields_reconstruction => Physics.LiSixQuarkResidual.onFields_reconstruction
assert_compatible GUT.LiSixQuarkResidual.physicalEquiv => Physics.LiSixQuarkResidual.physicalEquiv
assert_compatible GUT.LiSixQuarkResidual.physicalEquiv.eq_1 => Physics.LiSixQuarkResidual.physicalEquiv.eq_1
assert_compatible GUT.LiSixQuarkResidual.physical_assembly_extraction => Physics.LiSixQuarkResidual.physical_assembly_extraction
assert_compatible GUT.LiSixQuarkResidual.physical_extraction_assembly => Physics.LiSixQuarkResidual.physical_extraction_assembly
assert_compatible GUT.LiSixQuarkResidual.scalar => Physics.LiSixQuarkResidual.scalar
assert_compatible GUT.LiSixQuarkResidual.scalarProbeEquiv => Physics.LiSixQuarkResidual.scalarProbeEquiv
assert_compatible GUT.LiSixQuarkResidual.scalarProbeEquiv.eq_1 => Physics.LiSixQuarkResidual.scalarProbeEquiv.eq_1
assert_compatible GUT.LiSixQuarkResidual.scalar_finrank => Physics.LiSixQuarkResidual.scalar_finrank
assert_compatible GUT.LiSixQuarkResidual.scalar_physical_agrees => Physics.LiSixQuarkResidual.scalar_physical_agrees
assert_compatible GUT.LiSixQuarkResidual.slots => Physics.LiSixQuarkResidual.slots
assert_compatible GUT.LiSixQuarkResidual.statisticsEquiv => Physics.LiSixQuarkResidual.statisticsEquiv
assert_compatible GUT.LiSixQuarkResidual.statisticsSubmodule => Physics.LiSixQuarkResidual.statisticsSubmodule
assert_compatible GUT.LiSixQuarkResidual.statistics_iff => Physics.LiSixQuarkResidual.statistics_iff
assert_compatible GUT.SixQuarkPermutationCompleteness.coordinatesEquiv.eq_1 => Physics.SixQuarkPermutationCompleteness.coordinatesEquiv.eq_1
