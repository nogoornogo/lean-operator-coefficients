import Physics.StandardModel.Operators.Dipole.DipoleSMCoefficient
import Physics.StandardModel.Operators.DipoleCoefficientCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleSMCoefficient instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleSMCoefficient.FullGroup => Physics.DipoleSMCoefficient.FullGroup,
  GUT.DipoleSMCoefficient.SectorB => Physics.DipoleSMCoefficient.SectorB,
  GUT.DipoleSMCoefficient.SectorW => Physics.DipoleSMCoefficient.SectorW,
  GUT.DipoleSMCoefficient.cancelCharges => Physics.DipoleSMCoefficient.cancelCharges,
  GUT.DipoleSMCoefficient.charged => Physics.DipoleSMCoefficient.charged,
  GUT.DipoleSMCoefficient.coefficientEquiv => Physics.DipoleSMCoefficient.coefficientEquiv,
  GUT.DipoleSMCoefficient.equiv => Physics.DipoleSMCoefficient.equiv,
  GUT.DipoleSMCoefficient.equivB => Physics.DipoleSMCoefficient.equivB,
  GUT.DipoleSMCoefficient.equivW => Physics.DipoleSMCoefficient.equivW,
  GUT.DipoleSMCoefficient.exists_nonzero_iff => Physics.DipoleSMCoefficient.exists_nonzero_iff,
  GUT.DipoleSMCoefficient.onFieldsB => Physics.DipoleSMCoefficient.onFieldsB,
  GUT.DipoleSMCoefficient.onFieldsW => Physics.DipoleSMCoefficient.onFieldsW,
  GUT.DipoleSMCoefficient.ordered => Physics.DipoleSMCoefficient.ordered,
  GUT.DipoleSMCoefficient.orderedB => Physics.DipoleSMCoefficient.orderedB,
  GUT.DipoleSMCoefficient.orderedW => Physics.DipoleSMCoefficient.orderedW,
  GUT.DipoleSMCoefficient.projection => Physics.DipoleSMCoefficient.projection,
  GUT.DipoleSMCoefficient.projection_surjective => Physics.DipoleSMCoefficient.projection_surjective,
  GUT.StandardSMGaugeTensor.phase.eq_1 => Physics.StandardSMGaugeTensor.phase.eq_1
]

assert_compatible GUT.DipoleSMCoefficient.FullGroup => Physics.DipoleSMCoefficient.FullGroup
assert_compatible GUT.DipoleSMCoefficient.SectorB => Physics.DipoleSMCoefficient.SectorB
assert_compatible GUT.DipoleSMCoefficient.SectorW => Physics.DipoleSMCoefficient.SectorW
assert_compatible GUT.DipoleSMCoefficient.cancelCharges => Physics.DipoleSMCoefficient.cancelCharges
assert_compatible GUT.DipoleSMCoefficient.charged => Physics.DipoleSMCoefficient.charged
assert_compatible GUT.DipoleSMCoefficient.coefficientEquiv => Physics.DipoleSMCoefficient.coefficientEquiv
assert_compatible GUT.DipoleSMCoefficient.equiv => Physics.DipoleSMCoefficient.equiv
assert_compatible GUT.DipoleSMCoefficient.equivB => Physics.DipoleSMCoefficient.equivB
assert_compatible GUT.DipoleSMCoefficient.equivW => Physics.DipoleSMCoefficient.equivW
assert_compatible GUT.DipoleSMCoefficient.exists_nonzero_iff => Physics.DipoleSMCoefficient.exists_nonzero_iff
assert_compatible GUT.DipoleSMCoefficient.onFieldsB => Physics.DipoleSMCoefficient.onFieldsB
assert_compatible GUT.DipoleSMCoefficient.onFieldsW => Physics.DipoleSMCoefficient.onFieldsW
assert_compatible GUT.DipoleSMCoefficient.ordered => Physics.DipoleSMCoefficient.ordered
assert_compatible GUT.DipoleSMCoefficient.orderedB => Physics.DipoleSMCoefficient.orderedB
assert_compatible GUT.DipoleSMCoefficient.orderedW => Physics.DipoleSMCoefficient.orderedW
assert_compatible GUT.DipoleSMCoefficient.projection => Physics.DipoleSMCoefficient.projection
assert_compatible GUT.DipoleSMCoefficient.projection_surjective => Physics.DipoleSMCoefficient.projection_surjective
assert_compatible GUT.StandardSMGaugeTensor.phase.eq_1 => Physics.StandardSMGaugeTensor.phase.eq_1
