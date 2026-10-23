import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkResidual
import Physics.StandardModel.Operators.HeeckLeSixQuarkLocalBasis
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.DeltaBTwoFlavorOneGeneration
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkResidual instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkLocalBasis.orbitInvariant.eq_1 => Physics.HeeckLeSixQuarkLocalBasis.orbitInvariant.eq_1,
  GUT.HeeckLeSixQuarkResidual.OrbitHom => Physics.HeeckLeSixQuarkResidual.OrbitHom,
  GUT.HeeckLeSixQuarkResidual.StatisticsHom => Physics.HeeckLeSixQuarkResidual.StatisticsHom,
  GUT.HeeckLeSixQuarkResidual.assembleHom => Physics.HeeckLeSixQuarkResidual.assembleHom,
  GUT.HeeckLeSixQuarkResidual.coefficientEquiv => Physics.HeeckLeSixQuarkResidual.coefficientEquiv,
  GUT.HeeckLeSixQuarkResidual.extractHom => Physics.HeeckLeSixQuarkResidual.extractHom,
  GUT.HeeckLeSixQuarkResidual.homEquiv => Physics.HeeckLeSixQuarkResidual.homEquiv,
  GUT.HeeckLeSixQuarkResidual.literal_local_assembly => Physics.HeeckLeSixQuarkResidual.literal_local_assembly,
  GUT.HeeckLeSixQuarkResidual.onFieldsEquiv => Physics.HeeckLeSixQuarkResidual.onFieldsEquiv,
  GUT.HeeckLeSixQuarkResidual.onFields_reconstruction => Physics.HeeckLeSixQuarkResidual.onFields_reconstruction,
  GUT.HeeckLeSixQuarkResidual.physicalEquiv => Physics.HeeckLeSixQuarkResidual.physicalEquiv,
  GUT.HeeckLeSixQuarkResidual.physicalEquiv.eq_1 => Physics.HeeckLeSixQuarkResidual.physicalEquiv.eq_1,
  GUT.HeeckLeSixQuarkResidual.physical_assembly_extraction => Physics.HeeckLeSixQuarkResidual.physical_assembly_extraction,
  GUT.HeeckLeSixQuarkResidual.physical_extraction_assembly => Physics.HeeckLeSixQuarkResidual.physical_extraction_assembly,
  GUT.HeeckLeSixQuarkResidual.scalar => Physics.HeeckLeSixQuarkResidual.scalar,
  GUT.HeeckLeSixQuarkResidual.scalarProbeEquiv => Physics.HeeckLeSixQuarkResidual.scalarProbeEquiv,
  GUT.HeeckLeSixQuarkResidual.scalarProbeEquiv.eq_1 => Physics.HeeckLeSixQuarkResidual.scalarProbeEquiv.eq_1,
  GUT.HeeckLeSixQuarkResidual.scalar_finrank => Physics.HeeckLeSixQuarkResidual.scalar_finrank,
  GUT.HeeckLeSixQuarkResidual.scalar_physical_agrees => Physics.HeeckLeSixQuarkResidual.scalar_physical_agrees,
  GUT.HeeckLeSixQuarkResidual.slots => Physics.HeeckLeSixQuarkResidual.slots,
  GUT.HeeckLeSixQuarkResidual.statisticsEquiv => Physics.HeeckLeSixQuarkResidual.statisticsEquiv,
  GUT.HeeckLeSixQuarkResidual.statisticsSubmodule => Physics.HeeckLeSixQuarkResidual.statisticsSubmodule,
  GUT.HeeckLeSixQuarkResidual.statistics_iff => Physics.HeeckLeSixQuarkResidual.statistics_iff
]

assert_compatible GUT.HeeckLeSixQuarkLocalBasis.orbitInvariant.eq_1 => Physics.HeeckLeSixQuarkLocalBasis.orbitInvariant.eq_1
assert_compatible GUT.HeeckLeSixQuarkResidual.OrbitHom => Physics.HeeckLeSixQuarkResidual.OrbitHom
assert_compatible GUT.HeeckLeSixQuarkResidual.StatisticsHom => Physics.HeeckLeSixQuarkResidual.StatisticsHom
assert_compatible GUT.HeeckLeSixQuarkResidual.assembleHom => Physics.HeeckLeSixQuarkResidual.assembleHom
assert_compatible GUT.HeeckLeSixQuarkResidual.coefficientEquiv => Physics.HeeckLeSixQuarkResidual.coefficientEquiv
assert_compatible GUT.HeeckLeSixQuarkResidual.extractHom => Physics.HeeckLeSixQuarkResidual.extractHom
assert_compatible GUT.HeeckLeSixQuarkResidual.homEquiv => Physics.HeeckLeSixQuarkResidual.homEquiv
assert_compatible GUT.HeeckLeSixQuarkResidual.literal_local_assembly => Physics.HeeckLeSixQuarkResidual.literal_local_assembly
assert_compatible GUT.HeeckLeSixQuarkResidual.onFieldsEquiv => Physics.HeeckLeSixQuarkResidual.onFieldsEquiv
assert_compatible GUT.HeeckLeSixQuarkResidual.onFields_reconstruction => Physics.HeeckLeSixQuarkResidual.onFields_reconstruction
assert_compatible GUT.HeeckLeSixQuarkResidual.physicalEquiv => Physics.HeeckLeSixQuarkResidual.physicalEquiv
assert_compatible GUT.HeeckLeSixQuarkResidual.physicalEquiv.eq_1 => Physics.HeeckLeSixQuarkResidual.physicalEquiv.eq_1
assert_compatible GUT.HeeckLeSixQuarkResidual.physical_assembly_extraction => Physics.HeeckLeSixQuarkResidual.physical_assembly_extraction
assert_compatible GUT.HeeckLeSixQuarkResidual.physical_extraction_assembly => Physics.HeeckLeSixQuarkResidual.physical_extraction_assembly
assert_compatible GUT.HeeckLeSixQuarkResidual.scalar => Physics.HeeckLeSixQuarkResidual.scalar
assert_compatible GUT.HeeckLeSixQuarkResidual.scalarProbeEquiv => Physics.HeeckLeSixQuarkResidual.scalarProbeEquiv
assert_compatible GUT.HeeckLeSixQuarkResidual.scalarProbeEquiv.eq_1 => Physics.HeeckLeSixQuarkResidual.scalarProbeEquiv.eq_1
assert_compatible GUT.HeeckLeSixQuarkResidual.scalar_finrank => Physics.HeeckLeSixQuarkResidual.scalar_finrank
assert_compatible GUT.HeeckLeSixQuarkResidual.scalar_physical_agrees => Physics.HeeckLeSixQuarkResidual.scalar_physical_agrees
assert_compatible GUT.HeeckLeSixQuarkResidual.slots => Physics.HeeckLeSixQuarkResidual.slots
assert_compatible GUT.HeeckLeSixQuarkResidual.statisticsEquiv => Physics.HeeckLeSixQuarkResidual.statisticsEquiv
assert_compatible GUT.HeeckLeSixQuarkResidual.statisticsSubmodule => Physics.HeeckLeSixQuarkResidual.statisticsSubmodule
assert_compatible GUT.HeeckLeSixQuarkResidual.statistics_iff => Physics.HeeckLeSixQuarkResidual.statistics_iff
