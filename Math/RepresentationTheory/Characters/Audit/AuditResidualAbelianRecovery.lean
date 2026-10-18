import Math.RepresentationTheory.Characters.ResidualAbelianRecovery
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Residual Abelian recovery imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.ResidualAbelianRecovery.jointSpaceEquiv,
    ``Math.ResidualAbelianRecovery.sector_unitary,
    ``Math.ResidualAbelianRecovery.eval_circleCoefficients,
    ``Math.ResidualAbelianRecovery.joint_profile,
    ``Math.ResidualAbelianRecovery.index_eq_iff_joint_multiplicities]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Residual Abelian recovery: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Residual Abelian recovery: layer and {declarations.length} strict axiom checks passed"
