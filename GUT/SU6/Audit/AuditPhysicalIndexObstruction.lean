import GUT.SU6.SelectionRules.Models.PhysicalIndexObstruction
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU6PhysicalIndexObstruction.single_charge_eq,
    ``GUT.SU6PhysicalIndexObstruction.profiles_compatible,
    ``GUT.SU6PhysicalIndexObstruction.pure_charge_equalities,
    ``GUT.SU6PhysicalIndexObstruction.pure_qque_neutral,
    ``GUT.SU6PhysicalIndexObstruction.no_pure_nontrivial_target,
    ``GUT.SU6PhysicalIndexObstruction.searchCharges,
    ``GUT.SU6PhysicalIndexObstruction.no_search_target,
    ``GUT.SU6PhysicalIndexObstruction.cyclicLabel,
    ``GUT.SU6PhysicalIndexObstruction.cyclicLabel_injective,
    ``GUT.SU6PhysicalIndexObstruction.normalizedCharges,
    ``GUT.SU6PhysicalIndexObstruction.normalized_dictionary,
    ``GUT.SU6PhysicalIndexObstruction.no_normalized_target]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Physical index: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Physical index: {ds.length} strict transitive checks passed"
