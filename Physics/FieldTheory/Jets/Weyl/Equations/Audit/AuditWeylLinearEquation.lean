import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Weyl.Equations.WeylLinearEquation
import Physics.FieldTheory.Jets.Weyl.Equations.WeylEquationControls
import Physics.FieldTheory.Jets.Weyl.Equations.WeylEquationIBP

/-! Strict transitive audit of linear EOM and actual Weyl source connections. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.WeylLinearEquation.Group,
    ``Physics.WeylLinearEquation.Coordinates,
    ``Physics.WeylLinearEquation.Spinor,
    ``Physics.WeylLinearEquation.Jets,
    ``Physics.WeylLinearEquation.Equations,
    ``Physics.WeylLinearEquation.contractMatrix,
    ``Physics.WeylLinearEquation.contract,
    ``Physics.WeylLinearEquation.contract_matrix,
    ``Physics.WeylLinearEquation.contract_covariant,
    ``Physics.WeylLinearEquation.frame,
    ``Physics.WeylLinearEquation.expand,
    ``Physics.WeylLinearEquation.frame_covariant,
    ``Physics.WeylLinearEquation.seed,
    ``Physics.WeylLinearEquation.seed_covariant,
    ``Physics.WeylLinearEquation.relations,
    ``Physics.WeylLinearEquation.Generator,
    ``Physics.WeylLinearEquation.action,
    ``Physics.WeylLinearEquation.descendant_zero,
    ``Physics.WeylLinearEquation.row,
    ``Physics.WeylLinearEquation.field_expansion,
    ``Physics.WeylLinearEquation.shift_field,
    ``Physics.WeylLinearEquation.seed_row_zero,
    ``Physics.WeylLinearEquation.seed_row_one,
    ``Physics.WeylLinearEquation.seed_row_ne_zero,
    ``Physics.WeylLinearEquation.wave_zero_relation,
    ``Physics.WeylLinearEquation.wave_one_relation,
    ``Physics.WeylLinearEquation.wave_descendants,
    ``Physics.WeylLinearEquation.nullPoint,
    ``Physics.WeylLinearEquation.probe,
    ``Physics.WeylLinearEquation.probe_ofSymbols,
    ``Physics.WeylLinearEquation.probe_multiple,
    ``Physics.WeylLinearEquation.probe_shift,
    ``Physics.WeylLinearEquation.probe_seed,
    ``Physics.WeylLinearEquation.probe_annihilates,
    ``Physics.WeylLinearEquation.onShellProbe,
    ``Physics.WeylLinearEquation.higher_jet_survives,
    ``Physics.WeylLinearEquation.odd_higher_jet_survives,
    ``Physics.WeylLinearEquation.spectatorSeed,
    ``Physics.WeylLinearEquation.spectatorEquations,
    ``Physics.WeylLinearEquation.spectator_covariant,
    ``Physics.WeylLinearEquation.Algebra,
    ``Physics.WeylLinearEquation.projection,
    ``Physics.WeylLinearEquation.algebraAction,
    ``Physics.WeylLinearEquation.equation_zero,
    ``Physics.WeylLinearEquation.equation_descendant_zero,
    ``Physics.WeylLinearEquation.detect,
    ``Physics.WeylLinearEquation.higher_mixed_jet_survives,
    ``Physics.WeylLinearEquation.projection_derivative,
    ``Physics.WeylLinearEquation.finite_source,
    ``Physics.WeylLinearEquation.sourceEquiv,
    ``Physics.WeylLinearEquation.coefficientEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Linear EOM/Weyl connection: {ds.length} strict transitive checks passed"
