import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraSignedConvention
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Signed adapter imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraSignedConvention.inverseCharge,
    ``Physics.DevMohapatraSignedConvention.inverse_left,
    ``Physics.DevMohapatraSignedConvention.inverse_right,
    ``Physics.DevMohapatraSignedConvention.components,
    ``Physics.DevMohapatraSignedConvention.inversePair,
    ``Physics.DevMohapatraSignedConvention.inversePair_eq,
    ``Physics.DevMohapatraSignedConvention.source_mass,
    ``Physics.DevMohapatraSignedConvention.source_vertex,
    ``Physics.DevMohapatraSignedConvention.inverseDownCurrent,
    ``Physics.DevMohapatraSignedConvention.inverseDownCurrent_eq,
    ``Physics.DevMohapatraSignedConvention.inverseOperator,
    ``Physics.DevMohapatraSignedConvention.inverseOperator_eq,
    ``Physics.DevMohapatraSignedConvention.generated_inverse,
    ``Physics.DevMohapatraSignedConvention.consistent_bilinear_rescaling]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Signed adapter: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Signed adapter: {ds.length} strict transitive checks passed"
