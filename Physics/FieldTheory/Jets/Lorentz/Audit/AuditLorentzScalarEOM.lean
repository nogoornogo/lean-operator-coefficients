import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Scalar.Inputs.MasslessScalarEOM

/-! Strict transitive audit of Actual Lorentz, Weyl and massless scalar consumers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.LorentzDirections.Group,
    ``Physics.LorentzDirections.Coordinates,
    ``Physics.LorentzDirections.Mat,
    ``Physics.LorentzDirections.pauli,
    ``Physics.LorentzDirections.fromPauli,
    ``Physics.LorentzDirections.pauliEquiv,
    ``Physics.LorentzDirections.matrixAction,
    ``Physics.LorentzDirections.matrixAction_apply,
    ``Physics.LorentzDirections.vector,
    ``Physics.LorentzDirections.basisEquiv,
    ``Physics.LorentzDirections.dualEquiv,
    ``Physics.LorentzDirections.direction,
    ``Physics.LorentzDirections.direction_single,
    ``Physics.LorentzDirections.pauli_vector,
    ``Physics.LorentzDirections.quadratic,
    ``Physics.LorentzDirections.det_pauli,
    ``Physics.LorentzDirections.quadratic_invariant,
    ``Physics.LorentzDirections.wave,
    ``Physics.LorentzDirections.eval_linearForm,
    ``Physics.LorentzDirections.eval_symbolMap_X,
    ``Physics.LorentzDirections.wave_invariant,
    ``Physics.LorentzDirections.outer,
    ``Physics.LorentzDirections.left_right_matrix,
    ``Physics.LorentzDirections.pauli_real_hermitian,
    ``Physics.LorentzDirections.preserves_hermitian,
    ``Physics.LorentzDirections.pauli_conjugate,
    ``Physics.LorentzDirections.vector_preserves_real,
    ``Physics.LorentzJetIBP.Group,
    ``Physics.LorentzJetIBP.scalarField,
    ``Physics.LorentzJetIBP.spinorBasis,
    ``Physics.LorentzJetIBP.weyl,
    ``Physics.LorentzJetIBP.weyl_basis,
    ``Physics.LorentzJetIBP.weyl_derivative,
    ``Physics.LorentzJetIBP.scalarAction,
    ``Physics.LorentzJetIBP.kinetic,
    ``Physics.LorentzJetIBP.waveField,
    ``Physics.LorentzJetIBP.kinetic_formula,
    ``Physics.LorentzJetIBP.kinetic_invariant,
    ``Physics.LorentzJetIBP.waveField_invariant,
    ``Physics.LorentzJetIBP.scalarCoefficientEquiv,
    ``Physics.LorentzJetIBP.weylMixedCoefficientEquiv,
    ``Physics.LorentzJetIBP.weylSourceEquiv,
    ``Physics.MasslessScalarEOM.equation,
    ``Physics.MasslessScalarEOM.Generator,
    ``Physics.MasslessScalarEOM.Algebra,
    ``Physics.MasslessScalarEOM.projection,
    ``Physics.MasslessScalarEOM.trace_zero,
    ``Physics.MasslessScalarEOM.descendants_zero,
    ``Physics.MasslessScalarEOM.waveField_zero,
    ``Physics.MasslessScalarEOM.nullPoint,
    ``Physics.MasslessScalarEOM.nullPoint_wave,
    ``Physics.MasslessScalarEOM.higher_time_jet_survives,
    ``Physics.MasslessScalarEOM.higher_time_field_survives,
    ``Physics.MasslessScalarEOM.presentationEquiv,
    ``Physics.MasslessScalarEOM.action,
    ``Physics.MasslessScalarEOM.derivative_covariance,
    ``Physics.MasslessScalarEOM.coefficientEquiv,
    ``Physics.MasslessScalarEOM.combinedSourceEquiv,
    ``Physics.MasslessScalarEOM.combinedRepresentationEquiv,
    ``Physics.MasslessScalarEOM.field,
    ``Physics.MasslessScalarEOM.firstJet,
    ``Physics.MasslessScalarEOM.current,
    ``Physics.MasslessScalarEOM.waveField_formula,
    ``Physics.MasslessScalarEOM.divergence_current,
    ``Physics.MasslessScalarEOM.fullRelations,
    ``Physics.MasslessScalarEOM.kinetic_mem_relations,
    ``Physics.MasslessScalarEOM.kinetic_zero_mod_ibp]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Actual Lorentz, Weyl and massless scalar consumers: {ds.length} strict transitive checks passed"
