import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenLocalTransport
import Physics.StandardModel.Operators.BnvSevenFieldTensor
import Physics.StandardModel.Operators.BnvSevenGaugeTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenLocalTransport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenLocalTransport.GaugeCoreCarrier => Physics.BnvSevenLocalTransport.GaugeCoreCarrier,
  GUT.BnvSevenLocalTransport.Index => Physics.BnvSevenLocalTransport.Index,
  GUT.BnvSevenLocalTransport.WeakCoreCarrier => Physics.BnvSevenLocalTransport.WeakCoreCarrier,
  GUT.BnvSevenLocalTransport.core => Physics.BnvSevenLocalTransport.core,
  GUT.BnvSevenLocalTransport.corePairing => Physics.BnvSevenLocalTransport.corePairing,
  GUT.BnvSevenLocalTransport.coreProbe => Physics.BnvSevenLocalTransport.coreProbe,
  GUT.BnvSevenLocalTransport.corePullback => Physics.BnvSevenLocalTransport.corePullback,
  GUT.BnvSevenLocalTransport.core_pairing_probe => Physics.BnvSevenLocalTransport.core_pairing_probe,
  GUT.BnvSevenLocalTransport.core_reconstruction => Physics.BnvSevenLocalTransport.core_reconstruction,
  GUT.BnvSevenLocalTransport.cover => Physics.BnvSevenLocalTransport.cover,
  GUT.BnvSevenLocalTransport.cover.eq_1 => Physics.BnvSevenLocalTransport.cover.eq_1,
  GUT.BnvSevenLocalTransport.cover_surjective => Physics.BnvSevenLocalTransport.cover_surjective,
  GUT.BnvSevenLocalTransport.flavorAlongEquiv => Physics.BnvSevenLocalTransport.flavorAlongEquiv,
  GUT.BnvSevenLocalTransport.flavorEquiv => Physics.BnvSevenLocalTransport.flavorEquiv,
  GUT.BnvSevenLocalTransport.gaugeCore => Physics.BnvSevenLocalTransport.gaugeCore,
  GUT.BnvSevenLocalTransport.gaugeEquiv => Physics.BnvSevenLocalTransport.gaugeEquiv,
  GUT.BnvSevenLocalTransport.instAddCommGroupWeakCoreCarrier => Physics.BnvSevenLocalTransport.instAddCommGroupWeakCoreCarrier,
  GUT.BnvSevenLocalTransport.instDecidableEqIndex => Physics.BnvSevenLocalTransport.instDecidableEqIndex,
  GUT.BnvSevenLocalTransport.instFintypeIndex => Physics.BnvSevenLocalTransport.instFintypeIndex,
  GUT.BnvSevenLocalTransport.instModuleComplexWeakCoreCarrier => Physics.BnvSevenLocalTransport.instModuleComplexWeakCoreCarrier,
  GUT.BnvSevenLocalTransport.invariantEquiv => Physics.BnvSevenLocalTransport.invariantEquiv,
  GUT.BnvSevenLocalTransport.localEquiv => Physics.BnvSevenLocalTransport.localEquiv,
  GUT.BnvSevenLocalTransport.pairing => Physics.BnvSevenLocalTransport.pairing,
  GUT.BnvSevenLocalTransport.pairing_probe => Physics.BnvSevenLocalTransport.pairing_probe,
  GUT.BnvSevenLocalTransport.probe => Physics.BnvSevenLocalTransport.probe,
  GUT.BnvSevenLocalTransport.qddSpin => Physics.BnvSevenLocalTransport.qddSpin,
  GUT.BnvSevenLocalTransport.reconstruction => Physics.BnvSevenLocalTransport.reconstruction,
  GUT.BnvSevenLocalTransport.spinCore => Physics.BnvSevenLocalTransport.spinCore,
  GUT.BnvSevenLocalTransport.spinEquiv => Physics.BnvSevenLocalTransport.spinEquiv
]

assert_compatible GUT.BnvSevenLocalTransport.GaugeCoreCarrier => Physics.BnvSevenLocalTransport.GaugeCoreCarrier
assert_compatible GUT.BnvSevenLocalTransport.Index => Physics.BnvSevenLocalTransport.Index
assert_compatible GUT.BnvSevenLocalTransport.WeakCoreCarrier => Physics.BnvSevenLocalTransport.WeakCoreCarrier
assert_compatible GUT.BnvSevenLocalTransport.core => Physics.BnvSevenLocalTransport.core
assert_compatible GUT.BnvSevenLocalTransport.corePairing => Physics.BnvSevenLocalTransport.corePairing
assert_compatible GUT.BnvSevenLocalTransport.coreProbe => Physics.BnvSevenLocalTransport.coreProbe
assert_compatible GUT.BnvSevenLocalTransport.corePullback => Physics.BnvSevenLocalTransport.corePullback
assert_compatible GUT.BnvSevenLocalTransport.core_pairing_probe => Physics.BnvSevenLocalTransport.core_pairing_probe
assert_compatible GUT.BnvSevenLocalTransport.core_reconstruction => Physics.BnvSevenLocalTransport.core_reconstruction
assert_compatible GUT.BnvSevenLocalTransport.cover => Physics.BnvSevenLocalTransport.cover
assert_compatible GUT.BnvSevenLocalTransport.cover.eq_1 => Physics.BnvSevenLocalTransport.cover.eq_1
assert_compatible GUT.BnvSevenLocalTransport.cover_surjective => Physics.BnvSevenLocalTransport.cover_surjective
assert_compatible GUT.BnvSevenLocalTransport.flavorAlongEquiv => Physics.BnvSevenLocalTransport.flavorAlongEquiv
assert_compatible GUT.BnvSevenLocalTransport.flavorEquiv => Physics.BnvSevenLocalTransport.flavorEquiv
assert_compatible GUT.BnvSevenLocalTransport.gaugeCore => Physics.BnvSevenLocalTransport.gaugeCore
assert_compatible GUT.BnvSevenLocalTransport.gaugeEquiv => Physics.BnvSevenLocalTransport.gaugeEquiv
assert_compatible GUT.BnvSevenLocalTransport.instAddCommGroupWeakCoreCarrier => Physics.BnvSevenLocalTransport.instAddCommGroupWeakCoreCarrier
assert_compatible GUT.BnvSevenLocalTransport.instDecidableEqIndex => Physics.BnvSevenLocalTransport.instDecidableEqIndex
assert_compatible GUT.BnvSevenLocalTransport.instFintypeIndex => Physics.BnvSevenLocalTransport.instFintypeIndex
assert_compatible GUT.BnvSevenLocalTransport.instModuleComplexWeakCoreCarrier => Physics.BnvSevenLocalTransport.instModuleComplexWeakCoreCarrier
assert_compatible GUT.BnvSevenLocalTransport.invariantEquiv => Physics.BnvSevenLocalTransport.invariantEquiv
assert_compatible GUT.BnvSevenLocalTransport.localEquiv => Physics.BnvSevenLocalTransport.localEquiv
assert_compatible GUT.BnvSevenLocalTransport.pairing => Physics.BnvSevenLocalTransport.pairing
assert_compatible GUT.BnvSevenLocalTransport.pairing_probe => Physics.BnvSevenLocalTransport.pairing_probe
assert_compatible GUT.BnvSevenLocalTransport.probe => Physics.BnvSevenLocalTransport.probe
assert_compatible GUT.BnvSevenLocalTransport.qddSpin => Physics.BnvSevenLocalTransport.qddSpin
assert_compatible GUT.BnvSevenLocalTransport.reconstruction => Physics.BnvSevenLocalTransport.reconstruction
assert_compatible GUT.BnvSevenLocalTransport.spinCore => Physics.BnvSevenLocalTransport.spinCore
assert_compatible GUT.BnvSevenLocalTransport.spinEquiv => Physics.BnvSevenLocalTransport.spinEquiv
