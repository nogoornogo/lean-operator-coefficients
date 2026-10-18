import GUT.SU5.Matching.LightSpeciesCompleteness
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU5.LightSpeciesMaps.smEquiv_action,
    ``GUT.SU5.LightSpeciesMaps.sm_continuous,
    ``GUT.SU5.LightSpeciesMaps.sm_semisimple,
    ``GUT.SU5.LightSpeciesMaps.readSM,
    ``GUT.SU5.LightSpeciesMaps.insertSM,
    ``GUT.SU5.LightSpeciesMaps.quarkSM,
    ``GUT.SU5.LightSpeciesMaps.upSM,
    ``GUT.SU5.LightSpeciesMaps.electronSM,
    ``GUT.SU5.LightSpeciesExhaustion.read_insert_cross,
    ``GUT.SU5.LightSpeciesExhaustion.readQ_embed,
    ``GUT.SU5.LightSpeciesExhaustion.readU_embed,
    ``GUT.SU5.LightSpeciesExhaustion.readE_embed,
    ``GUT.SU5.LightSpeciesExhaustion.allQ_injective,
    ``GUT.SU5.LightSpeciesExhaustion.allU_injective,
    ``GUT.SU5.LightSpeciesExhaustion.allE_injective,
    ``GUT.SU5.LightSpeciesExhaustion.allQ_surjective,
    ``GUT.SU5.LightSpeciesExhaustion.allU_surjective,
    ``GUT.SU5.LightSpeciesExhaustion.allE_surjective,
    ``GUT.SU5.LightSpeciesExchange.coefficient_restrict,
    ``GUT.SU5.LightSpeciesExchange.current_cross,
    ``GUT.SU5.LightSpeciesExchange.left_cross,
    ``GUT.SU5.LightSpeciesExchange.right_cross,
    ``GUT.SU5.LightSpeciesExchange.coefficient_generations,
    ``GUT.SU5.LightSpeciesExchange.Q_action,
    ``GUT.SU5.LightSpeciesExchange.U_action,
    ``GUT.SU5.LightSpeciesExchange.E_action,
    ``GUT.SU5.LightSpeciesExchange.Q_h_action,
    ``GUT.SU5.LightSpeciesExchange.U_h_action,
    ``GUT.SU5.LightSpeciesExchange.E_h_action,
    ``GUT.SU5.LightSpeciesExchange.generations_sm,
    ``GUT.SU5.LightSpeciesExchange.sm_invariant,
    ``GUT.SU5.LightSpeciesExchange.h_invariant,
    ``GUT.SU5.LightSpeciesExchange.invariant,
    ``GUT.SU5.LightSpeciesCompleteness.generated_nonzero,
    ``GUT.SU5.LightSpeciesCompleteness.certificate_generated,
    ``GUT.SU5.LightSpeciesCompleteness.certificate_residualHom,
    ``GUT.SU5.LightSpeciesCompleteness.reconstruct,
    ``GUT.SU5.LightSpeciesCompleteness.residualHom_nonzero,
    ``GUT.SU5.LightSpeciesCompleteness.hasCoefficient,
    ``GUT.SU5.LightSpeciesCompleteness.hasResidualMap,
    ``GUT.SU5.LightSpeciesCompleteness.one_generation,
    ``GUT.SU5.LightSpeciesCompleteness.three_generations]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Joint light species: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Joint light species: {declarations.length} strict axiom checks passed"
