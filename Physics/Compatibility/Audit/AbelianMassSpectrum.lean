import Physics.FieldTheory.Mass.AbelianMassSpectrum
import Lean.Util.CollectAxioms
import Lean.Meta.Basic

/-! Old/new mass-spectrum names have definitionally equal values and the
same strict transitive axiom boundary. The legacy import warning is expected. -/

open Lean Lean.Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let names := [
    `radical_unitary, `radicalSpectrum, `radicalSpectrum_nonneg,
    `radicalSpectrum_eval, `radical_dual_spectrum_eq,
    `radical_dual_spectrum_eq_target, `source_target_of_radical_target,
    `coefficient_lower_bound, `exists_radical_vector_of_pos,
    `exists_zeroMode_of_pos]
  for suffix in names do
    let old := `GUT.AbelianMassSpectrum ++ suffix
    let current := `Physics.AbelianMassSpectrum ++ suffix
    let oldValue ← mkConstWithLevelParams old
    let currentValue ← mkConstWithLevelParams current
    unless ← isDefEq oldValue currentValue do
      throwError "Compatibility value changed: {old} / {current}"
    for name in [old, current] do
      for ax in (← collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Compatibility alias {name} uses unexpected axiom {ax}"
  logInfo m!"Mass spectrum compatibility: {names.length} value equalities, 20 strict axiom checks"

-- An unchanged old client and its migrated equivalent both elaborate.
example : @GUT.AbelianMassSpectrum.radicalSpectrum =
    @Physics.AbelianMassSpectrum.radicalSpectrum := rfl
