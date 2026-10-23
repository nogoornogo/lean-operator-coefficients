import Math.Audit.ImportOrigin
import Physics.StandardModel.Operators.Support.Decomposition.SMGenerationSupport

/-! Strict audit of the generation injection boundary, independently of later consumers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Generation support imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.SMGenerationSupport.generation_triple,
    ``Physics.SMGenerationSupport.generation_triple_presented_coefficient,
    ``Physics.SMGenerationSupport.spinInsert_injective,
    ``Physics.SMGenerationSupport.quark_six,
    ``Physics.SMGenerationSupport.quark_twelve,
    ``Physics.SMGenerationSupport.quark_eighteen,
    ``Physics.SMGenerationSupport.lepton_two,
    ``Physics.SMGenerationSupport.lepton_four,
    ``Physics.SMGenerationSupport.lepton_six]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Generation support {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Generation injection boundary: {ds.length} strict transitive checks passed"
