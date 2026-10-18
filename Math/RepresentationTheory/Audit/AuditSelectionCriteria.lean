import Math.LinearAlgebra.SelectionCriteria
import Math.RepresentationTheory.CyclicCharge
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

example : Math.SelectionCriteria.Forbidden (Fin 0 → ℂ) := by
  intro f; funext i; exact Fin.elim0 i

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Selection math imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.SelectionCriteria.forbidden_iff_not_allowed,
    ``Math.SelectionCriteria.allowed_equiv, ``Math.SelectionCriteria.ofEquiv,
    ``Math.SelectionCriteria.forbidden_family, ``Math.SelectionCriteria.allowed_family,
    ``Math.SelectionCriteria.forbidden_prod, ``Math.CyclicCharge.representation,
    ``Math.CyclicCharge.action, ``Math.CyclicCharge.neutral_iff,
    ``Math.CyclicCharge.sum_action, ``Math.CyclicCharge.dual_action]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Selection math {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Selection algebra: {ds.length} strict transitive checks passed"
