import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyHermitian
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyHermitian imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraHeavyHermitian.swapExternal,
    ``Physics.DevMohapatraHeavyHermitian.swapHeavy,
    ``Physics.DevMohapatraHeavyHermitian.swapExternal_involutive,
    ``Physics.DevMohapatraHeavyHermitian.swapHeavy_involutive,
    ``Physics.DevMohapatraHeavyHermitian.fieldConjugation,
    ``Physics.DevMohapatraHeavyHermitian.heavyConjugation,
    ``Physics.DevMohapatraHeavyHermitian.conjugation,
    ``Physics.DevMohapatraHeavyHermitian.conjugation_involutive,
    ``Physics.DevMohapatraHeavyHermitian.hc,
    ``Physics.DevMohapatraHeavyHermitian.hc_mul,
    ``Physics.DevMohapatraHeavyHermitian.hc_smul,
    ``Physics.DevMohapatraHeavyHermitian.hc_add,
    ``Physics.DevMohapatraHeavyHermitian.hc_sub,
    ``Physics.DevMohapatraHeavyHermitian.hc_involutive,
    ``Physics.DevMohapatraHeavyHermitian.fieldConjugation_u,
    ``Physics.DevMohapatraHeavyHermitian.fieldConjugation_d,
    ``Physics.DevMohapatraHeavyHermitian.fieldConjugation_s,
    ``Physics.DevMohapatraHeavyHermitian.hc_heavy,
    ``Physics.DevMohapatraHeavyHermitian.hc_external_generator,
    ``Physics.DevMohapatraHeavyHermitian.hc_generator,
    ``Physics.DevMohapatraHeavyHermitian.hc_pair,
    ``Physics.DevMohapatraHeavyHermitian.hc_sum,
    ``Physics.DevMohapatraHeavyHermitian.epsilon_real,
    ``Physics.DevMohapatraHeavyHermitian.hc_down,
    ``Physics.DevMohapatraHeavyHermitian.uw,
    ``Physics.DevMohapatraHeavyHermitian.dw,
    ``Physics.DevMohapatraHeavyHermitian.sw,
    ``Physics.DevMohapatraHeavyHermitian.ubw,
    ``Physics.DevMohapatraHeavyHermitian.dbw,
    ``Physics.DevMohapatraHeavyHermitian.sbw,
    ``Physics.DevMohapatraHeavyHermitian.conjugation_fields,
    ``Physics.DevMohapatraHeavyHermitian.include_down,
    ``Physics.DevMohapatraHeavyHermitian.include_current,
    ``Physics.DevMohapatraHeavyHermitian.U,
    ``Physics.DevMohapatraHeavyHermitian.Ub,
    ``Physics.DevMohapatraHeavyHermitian.D,
    ``Physics.DevMohapatraHeavyHermitian.Db,
    ``Physics.DevMohapatraHeavyHermitian.hc_U,
    ``Physics.DevMohapatraHeavyHermitian.hc_D,
    ``Physics.DevMohapatraHeavyHermitian.literalEffective,
    ``Physics.DevMohapatraHeavyHermitian.star_dictionary,
    ``Physics.DevMohapatraHeavyHermitian.U_apply,
    ``Physics.DevMohapatraHeavyHermitian.Ub_apply,
    ``Physics.DevMohapatraHeavyHermitian.sum_U_D,
    ``Physics.DevMohapatraHeavyHermitian.sum_Ub_Db,
    ``Physics.DevMohapatraHeavyHermitian.Db_commutes,
    ``Physics.DevMohapatraHeavyHermitian.mixed_color,
    ``Physics.DevMohapatraHeavyHermitian.sum_U_Ub,
    ``Physics.DevMohapatraHeavyHermitian.constant_dictionary,
    ``Physics.DevMohapatraHeavyHermitian.action_dictionary,
    ``Physics.DevMohapatraHeavyHermitian.literal_scalar_elimination,
    ``Physics.DevMohapatraHeavyHermitian.universal_hermitian,
    ``Physics.DevMohapatraHeavyHermitian.full_stationary,
    ``Physics.DevMohapatraHeavyHermitian.full_eliminated_action,
    ``Physics.DevMohapatraHeavyHermitian.holomorphic_full_action]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyHermitian: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyHermitian: {ds.length} strict transitive checks passed"
