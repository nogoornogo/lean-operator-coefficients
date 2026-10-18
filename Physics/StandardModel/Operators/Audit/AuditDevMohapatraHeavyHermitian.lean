import Physics.StandardModel.Operators.DevMohapatraHeavyHermitian
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyHermitian imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraHeavyHermitian.swapExternal,
    ``GUT.DevMohapatraHeavyHermitian.swapHeavy,
    ``GUT.DevMohapatraHeavyHermitian.swapExternal_involutive,
    ``GUT.DevMohapatraHeavyHermitian.swapHeavy_involutive,
    ``GUT.DevMohapatraHeavyHermitian.fieldConjugation,
    ``GUT.DevMohapatraHeavyHermitian.heavyConjugation,
    ``GUT.DevMohapatraHeavyHermitian.conjugation,
    ``GUT.DevMohapatraHeavyHermitian.conjugation_involutive,
    ``GUT.DevMohapatraHeavyHermitian.hc,
    ``GUT.DevMohapatraHeavyHermitian.hc_mul,
    ``GUT.DevMohapatraHeavyHermitian.hc_smul,
    ``GUT.DevMohapatraHeavyHermitian.hc_add,
    ``GUT.DevMohapatraHeavyHermitian.hc_sub,
    ``GUT.DevMohapatraHeavyHermitian.hc_involutive,
    ``GUT.DevMohapatraHeavyHermitian.fieldConjugation_u,
    ``GUT.DevMohapatraHeavyHermitian.fieldConjugation_d,
    ``GUT.DevMohapatraHeavyHermitian.fieldConjugation_s,
    ``GUT.DevMohapatraHeavyHermitian.hc_heavy,
    ``GUT.DevMohapatraHeavyHermitian.hc_external_generator,
    ``GUT.DevMohapatraHeavyHermitian.hc_generator,
    ``GUT.DevMohapatraHeavyHermitian.hc_pair,
    ``GUT.DevMohapatraHeavyHermitian.hc_sum,
    ``GUT.DevMohapatraHeavyHermitian.epsilon_real,
    ``GUT.DevMohapatraHeavyHermitian.hc_down,
    ``GUT.DevMohapatraHeavyHermitian.uw,
    ``GUT.DevMohapatraHeavyHermitian.dw,
    ``GUT.DevMohapatraHeavyHermitian.sw,
    ``GUT.DevMohapatraHeavyHermitian.ubw,
    ``GUT.DevMohapatraHeavyHermitian.dbw,
    ``GUT.DevMohapatraHeavyHermitian.sbw,
    ``GUT.DevMohapatraHeavyHermitian.conjugation_fields,
    ``GUT.DevMohapatraHeavyHermitian.include_down,
    ``GUT.DevMohapatraHeavyHermitian.include_current,
    ``GUT.DevMohapatraHeavyHermitian.U,
    ``GUT.DevMohapatraHeavyHermitian.Ub,
    ``GUT.DevMohapatraHeavyHermitian.D,
    ``GUT.DevMohapatraHeavyHermitian.Db,
    ``GUT.DevMohapatraHeavyHermitian.hc_U,
    ``GUT.DevMohapatraHeavyHermitian.hc_D,
    ``GUT.DevMohapatraHeavyHermitian.literalEffective,
    ``GUT.DevMohapatraHeavyHermitian.star_dictionary,
    ``GUT.DevMohapatraHeavyHermitian.U_apply,
    ``GUT.DevMohapatraHeavyHermitian.Ub_apply,
    ``GUT.DevMohapatraHeavyHermitian.sum_U_D,
    ``GUT.DevMohapatraHeavyHermitian.sum_Ub_Db,
    ``GUT.DevMohapatraHeavyHermitian.Db_commutes,
    ``GUT.DevMohapatraHeavyHermitian.mixed_color,
    ``GUT.DevMohapatraHeavyHermitian.sum_U_Ub,
    ``GUT.DevMohapatraHeavyHermitian.constant_dictionary,
    ``GUT.DevMohapatraHeavyHermitian.action_dictionary,
    ``GUT.DevMohapatraHeavyHermitian.literal_scalar_elimination,
    ``GUT.DevMohapatraHeavyHermitian.universal_hermitian,
    ``GUT.DevMohapatraHeavyHermitian.full_stationary,
    ``GUT.DevMohapatraHeavyHermitian.full_eliminated_action,
    ``GUT.DevMohapatraHeavyHermitian.holomorphic_full_action]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyHermitian: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyHermitian: {ds.length} strict transitive checks passed"
