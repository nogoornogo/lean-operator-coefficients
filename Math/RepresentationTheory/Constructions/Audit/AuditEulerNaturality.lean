import Math.Audit.ImportOrigin
import Math.Algebra.Variational.EulerNaturalityControls
import Math.Algebra.Variational.EulerNaturalityLiterature

/-! Source-owned inventory, strict transitive axiom and import-layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let owned : Array Name := #[`Math.LinearAlgebra.Selection.CoefficientTransport,
    `Math.Algebra.Jets.MixedJetPartial, `Math.Algebra.Jets.JetWordAdjoint,
    `Math.Algebra.Variational.SemanticEuler, `Math.Algebra.Jets.LinearJetSubstitution,
    `Math.Algebra.Variational.EulerNaturality, `Math.Algebra.Jets.BlockJetSubstitution,
    `Math.RepresentationTheory.Lagrangian.DensitySymmetry, `Math.RepresentationTheory.Lagrangian.StandardDensityAction,
    `Math.Algebra.Variational.EulerNaturalityControls, `Math.Algebra.Variational.EulerNaturalityLiterature]
  let mut checked : Nat := 0
  for (d,_) in env.constants.toList do
    if let some i := env.getModuleIdxFor? d then
      if owned.contains env.header.moduleNames[i]! then
        checked := checked+1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext,``Classical.choice,``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
  unless checked > 0 do throwError "Euler naturality audit inventory is empty"
  Lean.logInfo m!"Euler naturality mathematics: {checked} strict transitive checks passed"
