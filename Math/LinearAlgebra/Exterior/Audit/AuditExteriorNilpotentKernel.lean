import Math.LinearAlgebra.Exterior.ExteriorNilpotentKernel
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "ExteriorNilpotentKernel imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ExteriorNilpotentKernel.A,
    ``Math.ExteriorNilpotentKernel.P,
    ``Math.ExteriorNilpotentKernel.power_entries,
    ``Math.ExteriorNilpotentKernel.nilpotent,
    ``Math.ExteriorNilpotentKernel.inverse,
    ``Math.ExteriorNilpotentKernel.inverse_left,
    ``Math.ExteriorNilpotentKernel.inverse_right,
    ``Math.ExteriorNilpotentKernel.solution,
    ``Math.ExteriorNilpotentKernel.source_equation,
    ``Math.ExteriorNilpotentKernel.unique]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "ExteriorNilpotentKernel: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"ExteriorNilpotentKernel: {ds.length} strict transitive checks passed"
