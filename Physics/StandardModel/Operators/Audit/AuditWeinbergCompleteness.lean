import Physics.StandardModel.Operators.WeinbergGrading
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.WeinbergResidualHom.exchange_iff,
    ``GUT.WeinbergResidualHom.homEquiv,
    ``GUT.WeinbergResidualHom.eq_zero_of_subsingleton,
    ``GUT.WeinbergMajorana.evaluationEquiv,
    ``GUT.WeinbergMajorana.evaluation_formula,
    ``GUT.WeinbergScalarFlavor.exists_nonzero_iff_square_trivial,
    ``GUT.WeinbergScalarFlavor.oneGeneration_finrank,
    ``GUT.WeinbergScalarFlavor.sign_allowed,
    ``GUT.WeinbergModelSector.regroupEquiv,
    ``GUT.WeinbergModelSector.statisticsEquiv,
    ``GUT.WeinbergModelSector.homEquiv,
    ``GUT.WeinbergSMInterface.neutralEquiv,
    ``GUT.WeinbergSMInterface.projection_surjective,
    ``GUT.WeinbergSMInterface.homEquiv,
    ``GUT.WeinbergSMInterface.exists_nonzero_iff,
    ``GUT.WeinbergSMInterface.oneGenerationEquiv,
    ``GUT.WeinbergSMInterface.oneGeneration_finrank,
    ``GUT.WeinbergSMInterface.majoranaEquiv,
    ``GUT.WeinbergSMInterface.mass_evaluation,
    ``GUT.WeinbergSMInterface.mass_nonzero_iff,
    ``GUT.WeinbergSMInterface.mass_zero_vev,
    ``GUT.WeinbergSMInterface.onFieldsEquiv,
    ``GUT.WeinbergSMInterface.onFieldsMajoranaEquiv,
    ``GUT.WeinbergSMInterface.exists_on_fields_iff,
    ``GUT.WeinbergGrading.signature,
    ``GUT.WeinbergGrading.slot_scaling,
    ``GUT.WeinbergGrading.conjugate_lepton_scaling]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weinberg completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weinberg completeness: {declarations.length} strict transitive axiom checks passed"
