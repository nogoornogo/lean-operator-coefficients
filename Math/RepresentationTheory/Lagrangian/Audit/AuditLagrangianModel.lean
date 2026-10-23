import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Lagrangian.LagrangianModelControls
import Math.Algebra.Constructions.ScalarWeylYukawa

/-! Strict transitive audit of the new model surface and algebraic helpers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let owned := [`Math.LagrangianModel, `Math.LagrangianModelControls,
    `Math.ScalarWeylYukawa, `Math.LocalPolynomial.Expr.stable_of_euler_span,
    `Math.LocalPolynomial.Expr.scalar_stable_of_euler_span,
    `Math.LocalPolynomial.Expr.eval_sub,
    `Math.AllOrderDerivativeCoordinates.Presentation.target_values_iff]
  let mut checked : Nat := 0
  for (d,_) in env.constants.toList do
    if owned.any (fun ns => ns.isPrefixOf d) then
      checked := checked+1
      for ax in (← Lean.collectAxioms d) do
        unless [``propext,``Classical.choice,``Quot.sound].contains ax do
          throwError "Declaration {d} uses unexpected axiom {ax}"
  unless checked > 0 do throwError "Lagrangian model audit inventory is empty"
  Lean.logInfo m!"Lagrangian model mathematics: {checked} strict transitive checks passed"
