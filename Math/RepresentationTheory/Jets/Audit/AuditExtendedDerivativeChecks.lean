import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Jets.TwoSpeciesDerivativeChecks
import Math.Algebra.Jets.PolynomialJetConjugation
import Math.Algebra.Jets.SemilinearDifferentialRelations
import Math.LinearAlgebra.Selection.HermitianCoefficientChecks

/-! Strict whole-namespace inventories, including instances and helpers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  for ns in [`Math.InputPresentation, `Math.TwoSpeciesDerivativeChecks,
      `Math.PolynomialJetConjugation, `Math.SemilinearDifferentialRelations,
      `Math.HermitianCoefficientChecks] do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do
      throwError "Extended input inventory is empty: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
