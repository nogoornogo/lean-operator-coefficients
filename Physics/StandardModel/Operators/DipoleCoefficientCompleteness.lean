import Physics.StandardModel.Operators.Dipole.DipoleCoefficientCompleteness
import Physics.StandardModel.Operators.DipoleLocalSector
import Math.RepresentationTheory.InvariantEvaluation
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleCoefficientCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleCoefficientCompleteness.SectorB => Physics.DipoleCoefficientCompleteness.SectorB,
  GUT.DipoleCoefficientCompleteness.SectorW => Physics.DipoleCoefficientCompleteness.SectorW,
  GUT.DipoleCoefficientCompleteness.electron => Physics.DipoleCoefficientCompleteness.electron,
  GUT.DipoleCoefficientCompleteness.equiv => Physics.DipoleCoefficientCompleteness.equiv,
  GUT.DipoleCoefficientCompleteness.equiv.congr_simp => Physics.DipoleCoefficientCompleteness.equiv.congr_simp,
  GUT.DipoleCoefficientCompleteness.equivB => Physics.DipoleCoefficientCompleteness.equivB,
  GUT.DipoleCoefficientCompleteness.equivW => Physics.DipoleCoefficientCompleteness.equivW,
  GUT.DipoleCoefficientCompleteness.exists_nonzero_iff => Physics.DipoleCoefficientCompleteness.exists_nonzero_iff,
  GUT.DipoleCoefficientCompleteness.higgs => Physics.DipoleCoefficientCompleteness.higgs,
  GUT.DipoleCoefficientCompleteness.lepton => Physics.DipoleCoefficientCompleteness.lepton,
  GUT.DipoleCoefficientCompleteness.orderedB => Physics.DipoleCoefficientCompleteness.orderedB,
  GUT.DipoleCoefficientCompleteness.orderedW => Physics.DipoleCoefficientCompleteness.orderedW,
  GUT.DipoleCoefficientCompleteness.regroupB => Physics.DipoleCoefficientCompleteness.regroupB,
  GUT.DipoleCoefficientCompleteness.regroupW => Physics.DipoleCoefficientCompleteness.regroupW,
  GUT.DipoleCoefficientCompleteness.residualRegroup => Physics.DipoleCoefficientCompleteness.residualRegroup,
  GUT.DipoleCoefficientCompleteness.strengthB => Physics.DipoleCoefficientCompleteness.strengthB,
  GUT.DipoleCoefficientCompleteness.strengthW => Physics.DipoleCoefficientCompleteness.strengthW
]

assert_compatible GUT.DipoleCoefficientCompleteness.SectorB => Physics.DipoleCoefficientCompleteness.SectorB
assert_compatible GUT.DipoleCoefficientCompleteness.SectorW => Physics.DipoleCoefficientCompleteness.SectorW
assert_compatible GUT.DipoleCoefficientCompleteness.electron => Physics.DipoleCoefficientCompleteness.electron
assert_compatible GUT.DipoleCoefficientCompleteness.equiv => Physics.DipoleCoefficientCompleteness.equiv
assert_compatible GUT.DipoleCoefficientCompleteness.equiv.congr_simp => Physics.DipoleCoefficientCompleteness.equiv.congr_simp
assert_compatible GUT.DipoleCoefficientCompleteness.equivB => Physics.DipoleCoefficientCompleteness.equivB
assert_compatible GUT.DipoleCoefficientCompleteness.equivW => Physics.DipoleCoefficientCompleteness.equivW
assert_compatible GUT.DipoleCoefficientCompleteness.exists_nonzero_iff => Physics.DipoleCoefficientCompleteness.exists_nonzero_iff
assert_compatible GUT.DipoleCoefficientCompleteness.higgs => Physics.DipoleCoefficientCompleteness.higgs
assert_compatible GUT.DipoleCoefficientCompleteness.lepton => Physics.DipoleCoefficientCompleteness.lepton
assert_compatible GUT.DipoleCoefficientCompleteness.orderedB => Physics.DipoleCoefficientCompleteness.orderedB
assert_compatible GUT.DipoleCoefficientCompleteness.orderedW => Physics.DipoleCoefficientCompleteness.orderedW
assert_compatible GUT.DipoleCoefficientCompleteness.regroupB => Physics.DipoleCoefficientCompleteness.regroupB
assert_compatible GUT.DipoleCoefficientCompleteness.regroupW => Physics.DipoleCoefficientCompleteness.regroupW
assert_compatible GUT.DipoleCoefficientCompleteness.residualRegroup => Physics.DipoleCoefficientCompleteness.residualRegroup
assert_compatible GUT.DipoleCoefficientCompleteness.strengthB => Physics.DipoleCoefficientCompleteness.strengthB
assert_compatible GUT.DipoleCoefficientCompleteness.strengthW => Physics.DipoleCoefficientCompleteness.strengthW
