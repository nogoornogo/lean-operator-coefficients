import Math.LinearAlgebra.Exterior.ExteriorOdd
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "ExteriorOdd imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ExteriorOdd.A,
    ``Math.ExteriorOdd.Odd,
    ``Math.ExteriorOdd.generator_slide,
    ``Math.ExteriorOdd.even_central,
    ``Math.ExteriorOdd.odd_slide,
    ``Math.ExteriorOdd.anticommute,
    ``Math.ExteriorOdd.square_zero]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "ExteriorOdd: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"ExteriorOdd: {ds.length} strict transitive checks passed"
