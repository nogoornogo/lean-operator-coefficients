import Math.LinearAlgebra.Exterior.ExteriorLeftDerivative
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "ExteriorLeftDerivative imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ExteriorLeftDerivative.A,
    ``Math.ExteriorLeftDerivative.derivative,
    ``Math.ExteriorLeftDerivative.generator_mul,
    ``Math.ExteriorLeftDerivative.leibniz]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "ExteriorLeftDerivative: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"ExteriorLeftDerivative: {ds.length} strict transitive checks passed"
