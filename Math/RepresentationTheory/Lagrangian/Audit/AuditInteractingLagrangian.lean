import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Lagrangian.BosonicAllOrderCoordinates
import Math.RepresentationTheory.Lagrangian.InteractingLagrangianControls

/-! Strict transitive audit of the all-order classifier and all owned helpers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let owned := [`Math.AllOrderDerivativeCoordinates, `Math.DifferentialBasisRows,
    `Math.MixedJetMonomialBasis, `Math.LocalPolynomial.Expr,
    `Math.PolynomialPotentialClassification, `Math.InteractingLagrangianControls]
  let mut checked : Nat := 0
  for (d,_) in env.constants.toList do
    if owned.any (fun ns => ns.isPrefixOf d) then
      checked := checked+1
      for ax in (← Lean.collectAxioms d) do
        unless [``propext,``Classical.choice,``Quot.sound].contains ax do
          throwError "Declaration {d} uses unexpected axiom {ax}"
  unless checked > 0 do throwError "Interacting classifier audit inventory is empty"
  Lean.logInfo m!"Interacting Lagrangian classifier: {checked} strict transitive checks passed"
