import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticTwoCompleteness
import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourWitness
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticContractions

/-! Strict audits of the actual Lorentz controls, whole grade and quotient separator. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  for ns in [`Physics.LorentzFiniteControls, `Physics.ScalarQuarticTwoCompleteness,
      `Physics.ScalarQuarticFourWitness, `Physics.ScalarQuarticContractions] do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do
      throwError "Scalar Lorentz inventory is empty: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
