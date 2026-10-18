import Math.RepresentationTheory.FourSlotAlternation
import Math.RepresentationTheory.SymmetricInvariantPairing
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Four-slot alternation imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.FourSlotAlternation.ordered,
    ``Math.FourSlotAlternation.alternating,
    ``Math.FourSlotAlternation.alternating_slots,
    ``Math.FourSlotAlternation.alternating_invariant,
    ``Math.FourSlotAlternation.coefficient,
    ``Math.FourSlotAlternation.coefficient_slots,
    ``Math.FourSlotAlternation.coefficient_ne_zero,
    ``Math.FourSlotAlternation.coefficient_transport,
    ``Math.FourSlotAlternation.coefficient_transport_ne_zero,
    ``Math.SymmetricInvariantPairing.coefficient,
    ``Math.SymmetricInvariantPairing.apply_coefficient,
    ``Math.SymmetricInvariantPairing.swap,
    ``Math.SymmetricInvariantPairing.diagonal]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Four-slot alternation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Four-slot alternation: layer and {declarations.length} strict axiom checks passed"
