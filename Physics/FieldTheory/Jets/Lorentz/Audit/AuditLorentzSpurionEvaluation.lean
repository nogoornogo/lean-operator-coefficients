import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Lorentz.LorentzSpurionEvaluation

/-! Strict transitive audit of actual jet/spurion connections. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.LorentzSpurionEvaluation.Source,
    ``Physics.LorentzSpurionEvaluation.action,
    ``Physics.LorentzSpurionEvaluation.sourceEquiv,
    ``Physics.LorentzSpurionEvaluation.Coefficients,
    ``Physics.LorentzSpurionEvaluation.coefficientEquiv,
    ``Physics.LorentzSpurionEvaluation.evaluation,
    ``Physics.LorentzSpurionEvaluation.surjective,
    ``Physics.LorentzSpurionEvaluation.card_surjective,
    ``Physics.LorentzSpurionEvaluation.nonzero_iff,
    ``Physics.LorentzSpurionEvaluation.pullback_injective]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Jet/spurion connection: {ds.length} strict transitive checks passed"
