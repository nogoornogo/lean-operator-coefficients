import Physics.FieldTheory.Jets.Scalar.Inputs.MasslessScalarEOM
import Physics.FieldTheory.Jets.LorentzJetIBP
import Math.RepresentationTheory.JetEquationComparison
import Math.Algebra.JetEquationProbe
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.MasslessScalarEOM instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzJetIBP.waveField.eq_1 => Physics.LorentzJetIBP.waveField.eq_1,
  GUT.MasslessScalarEOM.Algebra => Physics.MasslessScalarEOM.Algebra,
  GUT.MasslessScalarEOM.Generator => Physics.MasslessScalarEOM.Generator,
  GUT.MasslessScalarEOM.action => Physics.MasslessScalarEOM.action,
  GUT.MasslessScalarEOM.coefficientEquiv => Physics.MasslessScalarEOM.coefficientEquiv,
  GUT.MasslessScalarEOM.combinedRepresentationEquiv => Physics.MasslessScalarEOM.combinedRepresentationEquiv,
  GUT.MasslessScalarEOM.combinedSourceEquiv => Physics.MasslessScalarEOM.combinedSourceEquiv,
  GUT.MasslessScalarEOM.current => Physics.MasslessScalarEOM.current,
  GUT.MasslessScalarEOM.current.eq_1 => Physics.MasslessScalarEOM.current.eq_1,
  GUT.MasslessScalarEOM.derivative_covariance => Physics.MasslessScalarEOM.derivative_covariance,
  GUT.MasslessScalarEOM.descendants_zero => Physics.MasslessScalarEOM.descendants_zero,
  GUT.MasslessScalarEOM.divergence_current => Physics.MasslessScalarEOM.divergence_current,
  GUT.MasslessScalarEOM.equation => Physics.MasslessScalarEOM.equation,
  GUT.MasslessScalarEOM.field => Physics.MasslessScalarEOM.field,
  GUT.MasslessScalarEOM.field.eq_1 => Physics.MasslessScalarEOM.field.eq_1,
  GUT.MasslessScalarEOM.firstJet => Physics.MasslessScalarEOM.firstJet,
  GUT.MasslessScalarEOM.firstJet.eq_1 => Physics.MasslessScalarEOM.firstJet.eq_1,
  GUT.MasslessScalarEOM.fullRelations => Physics.MasslessScalarEOM.fullRelations,
  GUT.MasslessScalarEOM.higher_time_field_survives => Physics.MasslessScalarEOM.higher_time_field_survives,
  GUT.MasslessScalarEOM.higher_time_jet_survives => Physics.MasslessScalarEOM.higher_time_jet_survives,
  GUT.MasslessScalarEOM.kinetic_mem_relations => Physics.MasslessScalarEOM.kinetic_mem_relations,
  GUT.MasslessScalarEOM.kinetic_zero_mod_ibp => Physics.MasslessScalarEOM.kinetic_zero_mod_ibp,
  GUT.MasslessScalarEOM.nullPoint => Physics.MasslessScalarEOM.nullPoint,
  GUT.MasslessScalarEOM.nullPoint.eq_1 => Physics.MasslessScalarEOM.nullPoint.eq_1,
  GUT.MasslessScalarEOM.nullPoint_wave => Physics.MasslessScalarEOM.nullPoint_wave,
  GUT.MasslessScalarEOM.presentationEquiv => Physics.MasslessScalarEOM.presentationEquiv,
  GUT.MasslessScalarEOM.projection => Physics.MasslessScalarEOM.projection,
  GUT.MasslessScalarEOM.trace_zero => Physics.MasslessScalarEOM.trace_zero,
  GUT.MasslessScalarEOM.waveField_formula => Physics.MasslessScalarEOM.waveField_formula,
  GUT.MasslessScalarEOM.waveField_zero => Physics.MasslessScalarEOM.waveField_zero
]

assert_compatible GUT.LorentzJetIBP.waveField.eq_1 => Physics.LorentzJetIBP.waveField.eq_1
assert_compatible GUT.MasslessScalarEOM.Algebra => Physics.MasslessScalarEOM.Algebra
assert_compatible GUT.MasslessScalarEOM.Generator => Physics.MasslessScalarEOM.Generator
assert_compatible GUT.MasslessScalarEOM.action => Physics.MasslessScalarEOM.action
assert_compatible GUT.MasslessScalarEOM.coefficientEquiv => Physics.MasslessScalarEOM.coefficientEquiv
assert_compatible GUT.MasslessScalarEOM.combinedRepresentationEquiv => Physics.MasslessScalarEOM.combinedRepresentationEquiv
assert_compatible GUT.MasslessScalarEOM.combinedSourceEquiv => Physics.MasslessScalarEOM.combinedSourceEquiv
assert_compatible GUT.MasslessScalarEOM.current => Physics.MasslessScalarEOM.current
assert_compatible GUT.MasslessScalarEOM.current.eq_1 => Physics.MasslessScalarEOM.current.eq_1
assert_compatible GUT.MasslessScalarEOM.derivative_covariance => Physics.MasslessScalarEOM.derivative_covariance
assert_compatible GUT.MasslessScalarEOM.descendants_zero => Physics.MasslessScalarEOM.descendants_zero
assert_compatible GUT.MasslessScalarEOM.divergence_current => Physics.MasslessScalarEOM.divergence_current
assert_compatible GUT.MasslessScalarEOM.equation => Physics.MasslessScalarEOM.equation
assert_compatible GUT.MasslessScalarEOM.field => Physics.MasslessScalarEOM.field
assert_compatible GUT.MasslessScalarEOM.field.eq_1 => Physics.MasslessScalarEOM.field.eq_1
assert_compatible GUT.MasslessScalarEOM.firstJet => Physics.MasslessScalarEOM.firstJet
assert_compatible GUT.MasslessScalarEOM.firstJet.eq_1 => Physics.MasslessScalarEOM.firstJet.eq_1
assert_compatible GUT.MasslessScalarEOM.fullRelations => Physics.MasslessScalarEOM.fullRelations
assert_compatible GUT.MasslessScalarEOM.higher_time_field_survives => Physics.MasslessScalarEOM.higher_time_field_survives
assert_compatible GUT.MasslessScalarEOM.higher_time_jet_survives => Physics.MasslessScalarEOM.higher_time_jet_survives
assert_compatible GUT.MasslessScalarEOM.kinetic_mem_relations => Physics.MasslessScalarEOM.kinetic_mem_relations
assert_compatible GUT.MasslessScalarEOM.kinetic_zero_mod_ibp => Physics.MasslessScalarEOM.kinetic_zero_mod_ibp
assert_compatible GUT.MasslessScalarEOM.nullPoint => Physics.MasslessScalarEOM.nullPoint
assert_compatible GUT.MasslessScalarEOM.nullPoint.eq_1 => Physics.MasslessScalarEOM.nullPoint.eq_1
assert_compatible GUT.MasslessScalarEOM.nullPoint_wave => Physics.MasslessScalarEOM.nullPoint_wave
assert_compatible GUT.MasslessScalarEOM.presentationEquiv => Physics.MasslessScalarEOM.presentationEquiv
assert_compatible GUT.MasslessScalarEOM.projection => Physics.MasslessScalarEOM.projection
assert_compatible GUT.MasslessScalarEOM.trace_zero => Physics.MasslessScalarEOM.trace_zero
assert_compatible GUT.MasslessScalarEOM.waveField_formula => Physics.MasslessScalarEOM.waveField_formula
assert_compatible GUT.MasslessScalarEOM.waveField_zero => Physics.MasslessScalarEOM.waveField_zero
