import Math.RepresentationTheory.SixSlotAlternation
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Layer and strict transitive axiom checks for six-slot alternating descent. -/

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Six-slot alternation imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.SixSlotAlternation.ordered,
    ``Math.SixSlotAlternation.alternating,
    ``Math.SixSlotAlternation.alternating_invariant,
    ``Math.SixSlotAlternation.coefficient,
    ``Math.SixSlotAlternation.coefficient_apply_ιMulti,
    ``Math.SixSlotAlternation.coefficient_ne_zero_of_evaluation]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-slot alternation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-slot alternation: layer and {declarations.length} strict axiom checks passed"
