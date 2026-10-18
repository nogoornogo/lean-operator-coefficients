import GUT.SU6.Yukawa.LightPlacementObstruction
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``GUT.SU6LightPlacementObstruction.all_yukawas_untouched,
    ``GUT.SU6LightPlacementObstruction.no_exact_light_omitting]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Light placement: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Light placement: {ds.length} strict transitive checks passed"
