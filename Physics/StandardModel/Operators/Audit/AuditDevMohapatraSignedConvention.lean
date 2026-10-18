import Physics.StandardModel.Operators.DevMohapatraSignedConvention
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Signed adapter imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraSignedConvention.inverseCharge,
    ``GUT.DevMohapatraSignedConvention.inverse_left,
    ``GUT.DevMohapatraSignedConvention.inverse_right,
    ``GUT.DevMohapatraSignedConvention.components,
    ``GUT.DevMohapatraSignedConvention.inversePair,
    ``GUT.DevMohapatraSignedConvention.inversePair_eq,
    ``GUT.DevMohapatraSignedConvention.source_mass,
    ``GUT.DevMohapatraSignedConvention.source_vertex,
    ``GUT.DevMohapatraSignedConvention.inverseDownCurrent,
    ``GUT.DevMohapatraSignedConvention.inverseDownCurrent_eq,
    ``GUT.DevMohapatraSignedConvention.inverseOperator,
    ``GUT.DevMohapatraSignedConvention.inverseOperator_eq,
    ``GUT.DevMohapatraSignedConvention.generated_inverse,
    ``GUT.DevMohapatraSignedConvention.consistent_bilinear_rescaling]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Signed adapter: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Signed adapter: {ds.length} strict transitive checks passed"
