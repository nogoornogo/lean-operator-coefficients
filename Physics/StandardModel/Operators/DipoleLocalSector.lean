import Physics.StandardModel.Operators.Dipole.DipoleLocalSector
import Physics.StandardModel.Gauge.DipoleGaugeTensor
import Physics.FieldTheory.Spinor.DipoleSpinorTensor
import Math.RepresentationTheory.NormalizedInvariantFactor
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleLocalSector instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleLocalSector.Group => Physics.DipoleLocalSector.Group,
  GUT.DipoleLocalSector.contractionB => Physics.DipoleLocalSector.contractionB,
  GUT.DipoleLocalSector.contractionB.eq_1 => Physics.DipoleLocalSector.contractionB.eq_1,
  GUT.DipoleLocalSector.contractionW => Physics.DipoleLocalSector.contractionW,
  GUT.DipoleLocalSector.contractionW.eq_1 => Physics.DipoleLocalSector.contractionW.eq_1,
  GUT.DipoleLocalSector.electron => Physics.DipoleLocalSector.electron,
  GUT.DipoleLocalSector.factoredB => Physics.DipoleLocalSector.factoredB,
  GUT.DipoleLocalSector.factoredW => Physics.DipoleLocalSector.factoredW,
  GUT.DipoleLocalSector.higgs => Physics.DipoleLocalSector.higgs,
  GUT.DipoleLocalSector.instAddCommGroupTensorProductComplexDoubletDualTriplet_physics => Physics.DipoleLocalSector.instAddCommGroupTensorProductComplexDoubletDualTriplet_physics,
  GUT.DipoleLocalSector.instAddCommGroupTensorProductComplexDoublet_physics => Physics.DipoleLocalSector.instAddCommGroupTensorProductComplexDoublet_physics,
  GUT.DipoleLocalSector.instAddCommGroupTensorProductComplexSpaceStrength => Physics.DipoleLocalSector.instAddCommGroupTensorProductComplexSpaceStrength,
  GUT.DipoleLocalSector.lepton => Physics.DipoleLocalSector.lepton,
  GUT.DipoleLocalSector.normalizedB => Physics.DipoleLocalSector.normalizedB,
  GUT.DipoleLocalSector.normalizedW => Physics.DipoleLocalSector.normalizedW,
  GUT.DipoleLocalSector.orderedB => Physics.DipoleLocalSector.orderedB,
  GUT.DipoleLocalSector.orderedW => Physics.DipoleLocalSector.orderedW,
  GUT.DipoleLocalSector.regroupB => Physics.DipoleLocalSector.regroupB,
  GUT.DipoleLocalSector.regroupW => Physics.DipoleLocalSector.regroupW,
  GUT.DipoleLocalSector.strengthB => Physics.DipoleLocalSector.strengthB,
  GUT.DipoleLocalSector.strengthW => Physics.DipoleLocalSector.strengthW,
  GUT.DipoleLocalSector.uniqueB => Physics.DipoleLocalSector.uniqueB,
  GUT.DipoleLocalSector.uniqueW => Physics.DipoleLocalSector.uniqueW,
  GUT.DipoleLocalSector.witnessB => Physics.DipoleLocalSector.witnessB,
  GUT.DipoleLocalSector.witnessB.eq_1 => Physics.DipoleLocalSector.witnessB.eq_1,
  GUT.DipoleLocalSector.witnessW => Physics.DipoleLocalSector.witnessW,
  GUT.DipoleLocalSector.witnessW.eq_1 => Physics.DipoleLocalSector.witnessW.eq_1
]

assert_compatible GUT.DipoleLocalSector.Group => Physics.DipoleLocalSector.Group
assert_compatible GUT.DipoleLocalSector.contractionB => Physics.DipoleLocalSector.contractionB
assert_compatible GUT.DipoleLocalSector.contractionB.eq_1 => Physics.DipoleLocalSector.contractionB.eq_1
assert_compatible GUT.DipoleLocalSector.contractionW => Physics.DipoleLocalSector.contractionW
assert_compatible GUT.DipoleLocalSector.contractionW.eq_1 => Physics.DipoleLocalSector.contractionW.eq_1
assert_compatible GUT.DipoleLocalSector.electron => Physics.DipoleLocalSector.electron
assert_compatible GUT.DipoleLocalSector.factoredB => Physics.DipoleLocalSector.factoredB
assert_compatible GUT.DipoleLocalSector.factoredW => Physics.DipoleLocalSector.factoredW
assert_compatible GUT.DipoleLocalSector.higgs => Physics.DipoleLocalSector.higgs
assert_compatible GUT.DipoleLocalSector.instAddCommGroupTensorProductComplexDoubletDualTriplet_physics => Physics.DipoleLocalSector.instAddCommGroupTensorProductComplexDoubletDualTriplet_physics
assert_compatible GUT.DipoleLocalSector.instAddCommGroupTensorProductComplexDoublet_physics => Physics.DipoleLocalSector.instAddCommGroupTensorProductComplexDoublet_physics
assert_compatible GUT.DipoleLocalSector.instAddCommGroupTensorProductComplexSpaceStrength => Physics.DipoleLocalSector.instAddCommGroupTensorProductComplexSpaceStrength
assert_compatible GUT.DipoleLocalSector.lepton => Physics.DipoleLocalSector.lepton
assert_compatible GUT.DipoleLocalSector.normalizedB => Physics.DipoleLocalSector.normalizedB
assert_compatible GUT.DipoleLocalSector.normalizedW => Physics.DipoleLocalSector.normalizedW
assert_compatible GUT.DipoleLocalSector.orderedB => Physics.DipoleLocalSector.orderedB
assert_compatible GUT.DipoleLocalSector.orderedW => Physics.DipoleLocalSector.orderedW
assert_compatible GUT.DipoleLocalSector.regroupB => Physics.DipoleLocalSector.regroupB
assert_compatible GUT.DipoleLocalSector.regroupW => Physics.DipoleLocalSector.regroupW
assert_compatible GUT.DipoleLocalSector.strengthB => Physics.DipoleLocalSector.strengthB
assert_compatible GUT.DipoleLocalSector.strengthW => Physics.DipoleLocalSector.strengthW
assert_compatible GUT.DipoleLocalSector.uniqueB => Physics.DipoleLocalSector.uniqueB
assert_compatible GUT.DipoleLocalSector.uniqueW => Physics.DipoleLocalSector.uniqueW
assert_compatible GUT.DipoleLocalSector.witnessB => Physics.DipoleLocalSector.witnessB
assert_compatible GUT.DipoleLocalSector.witnessB.eq_1 => Physics.DipoleLocalSector.witnessB.eq_1
assert_compatible GUT.DipoleLocalSector.witnessW => Physics.DipoleLocalSector.witnessW
assert_compatible GUT.DipoleLocalSector.witnessW.eq_1 => Physics.DipoleLocalSector.witnessW.eq_1
