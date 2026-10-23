import Physics.StandardModel.Operators.BaryonOne.Inputs.LiBasisMatrixCertificate
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Physics.LiBasisMatrixCertificate

example : LinearIndependent ℂ basis41 := basis41.linearIndependent
example : LinearIndependent ℂ basis44 := basis44.linearIndependent
example : matrix41.row 8 = 0 := by
  ext i; fin_cases i <;> norm_num [matrix41, Matrix.row]

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Matrix certificate imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``conversion, ``matrix38_apply, ``rank38, ``synthesis41, ``synthesis44,
    ``basis41, ``basis44, ``basis41_row, ``basis44_row,
    ``span41, ``span44, ``rank41, ``rank44, ``convertedBasis]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Li matrix {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li finite matrix certificates: {ds.length} strict axiom checks passed"
