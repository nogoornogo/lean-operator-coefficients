import Physics.FieldTheory.Yukawa.Mass.ProjectedYukawaEvaluation
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``Physics.ProjectedYukawa.diagonal_apply,
    ``Physics.ProjectedYukawa.mixed_apply, ``Physics.ProjectedYukawa.combine_apply,
    ``Physics.ProjectedYukawa.zeroBare_form, ``Physics.ProjectedYukawa.fiveFamily,
    ``Physics.ProjectedYukawa.fiveFamily_form, ``Physics.ProjectedYukawa.fiveForm_coordinates,
    ``Physics.ProjectedYukawa.flavorLinear, ``Physics.ProjectedYukawa.fiveForm_flavor_coordinates]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Projected Yukawa evaluation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Projected Yukawa evaluation: {declarations.length} strict axiom checks passed"
