import Physics.FieldTheory.Yukawa.ProjectedYukawaEvaluation
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.ProjectedYukawa.diagonal_apply,
    ``GUT.ProjectedYukawa.mixed_apply, ``GUT.ProjectedYukawa.combine_apply,
    ``GUT.ProjectedYukawa.zeroBare_form, ``GUT.ProjectedYukawa.fiveFamily,
    ``GUT.ProjectedYukawa.fiveFamily_form, ``GUT.ProjectedYukawa.fiveForm_coordinates,
    ``GUT.ProjectedYukawa.flavorLinear, ``GUT.ProjectedYukawa.fiveForm_flavor_coordinates]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Projected Yukawa evaluation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Projected Yukawa evaluation: {declarations.length} strict axiom checks passed"
