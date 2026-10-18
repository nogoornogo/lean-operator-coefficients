import GUT.SU5.Representations.CurrentBlocks
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU5.CurrentBlocks.direction,
    ``GUT.SU5.CurrentBlocks.curve_entry_hasDerivAt,
    ``GUT.SU5.CurrentBlocks.coefficient_hasDerivAt,
    ``GUT.SU5.CurrentBlocks.electron_quark_derivative,
    ``GUT.SU5.CurrentBlocks.quark_up_derivative,
    ``GUT.SU5.CurrentBlocks.electron_species,
    ``GUT.SU5.CurrentBlocks.quarkOut_species,
    ``GUT.SU5.CurrentBlocks.quarkIn_species,
    ``GUT.SU5.CurrentBlocks.up_species,
    ``GUT.SU5.CurrentBlocks.quarkCoordinate_eq,
    ``GUT.SU5.CurrentBlocks.upCoordinate_eq,
    ``GUT.SU5.CurrentBlocks.species_derivatives,
    ``GUT.SU5.CurrentBlocks.both_blocks_nonzero,
    ``GUT.SU5.CurrentBlocks.cross_block_formula,
    ``GUT.SU5.CurrentBlocks.selected_tangents_zero_of_entry_zero,
    ``GUT.SU5.CurrentBlocks.coefficients_at_zero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SU(5) current blocks: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"SU(5) current blocks: {declarations.length} strict axiom checks passed"
