import Math.LinearAlgebra.Constructions.AlgebraValuedQuadraticElimination
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Algebra-valued elimination imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.AlgebraValuedQuadraticElimination.pairedAction,
    ``Math.AlgebraValuedQuadraticElimination.solution,
    ``Math.AlgebraValuedQuadraticElimination.paired_shifted,
    ``Math.AlgebraValuedQuadraticElimination.paired_on_shell,
    ``Math.AlgebraValuedQuadraticElimination.paired_stationary_variation,
    ``Math.AlgebraValuedQuadraticElimination.majoranaAction,
    ``Math.AlgebraValuedQuadraticElimination.majorana_shifted,
    ``Math.AlgebraValuedQuadraticElimination.majorana_on_shell,
    ``Math.AlgebraValuedQuadraticElimination.majorana_stationary_variation]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Algebra-valued elimination: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Algebra-valued elimination: {ds.length} strict transitive checks passed"
