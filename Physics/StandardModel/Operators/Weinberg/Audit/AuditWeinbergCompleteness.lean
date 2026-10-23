import Physics.StandardModel.Operators.Weinberg.WeinbergGrading
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.WeinbergResidualHom.exchange_iff,
    ``Physics.WeinbergResidualHom.homEquiv,
    ``Physics.WeinbergResidualHom.eq_zero_of_subsingleton,
    ``Physics.WeinbergMajorana.evaluationEquiv,
    ``Physics.WeinbergMajorana.evaluation_formula,
    ``Physics.WeinbergScalarFlavor.exists_nonzero_iff_square_trivial,
    ``Physics.WeinbergScalarFlavor.oneGeneration_finrank,
    ``Physics.WeinbergScalarFlavor.sign_allowed,
    ``Physics.WeinbergModelSector.regroupEquiv,
    ``Physics.WeinbergModelSector.statisticsEquiv,
    ``Physics.WeinbergModelSector.homEquiv,
    ``Physics.WeinbergSMInterface.neutralEquiv,
    ``Physics.WeinbergSMInterface.projection_surjective,
    ``Physics.WeinbergSMInterface.homEquiv,
    ``Physics.WeinbergSMInterface.exists_nonzero_iff,
    ``Physics.WeinbergSMInterface.oneGenerationEquiv,
    ``Physics.WeinbergSMInterface.oneGeneration_finrank,
    ``Physics.WeinbergSMInterface.majoranaEquiv,
    ``Physics.WeinbergSMInterface.mass_evaluation,
    ``Physics.WeinbergSMInterface.mass_nonzero_iff,
    ``Physics.WeinbergSMInterface.mass_zero_vev,
    ``Physics.WeinbergSMInterface.onFieldsEquiv,
    ``Physics.WeinbergSMInterface.onFieldsMajoranaEquiv,
    ``Physics.WeinbergSMInterface.exists_on_fields_iff,
    ``Physics.WeinbergGrading.signature,
    ``Physics.WeinbergGrading.slot_scaling,
    ``Physics.WeinbergGrading.conjugate_lepton_scaling]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weinberg completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weinberg completeness: {declarations.length} strict transitive axiom checks passed"
