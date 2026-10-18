import Math.RepresentationTheory.ExternalInvariantTensor
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "External invariant tensor imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.ExternalInvariantTensor.external,
    ``Math.ExternalInvariantTensor.tensorEquiv,
    ``Math.ExternalInvariantTensor.externalEquiv,
    ``Math.ExternalInvariantTensor.regroupPair,
    ``Math.ExternalInvariantTensor.regroupFour,
    ``Math.ExternalInvariantTensor.coefficient,
    ``Math.ExternalInvariantTensor.coefficient_tmul,
    ``Math.ExternalInvariantTensor.coefficient_ne_zero,
    ``Math.ExternalInvariantTensor.comp_equiv_ne_zero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "External invariant tensor: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"External invariant tensor: layer and {declarations.length} strict axiom checks passed"
