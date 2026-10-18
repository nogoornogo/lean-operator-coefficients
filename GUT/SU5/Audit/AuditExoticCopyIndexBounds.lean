import GUT.SU5.SelectionRules.ExoticCopyIndexBounds
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU5.ExoticCopyIndexBounds.profiles,
    ``GUT.SU5.ExoticCopyIndexBounds.index,
    ``GUT.SU5.ExoticCopyIndexBounds.row_dictionary,
    ``GUT.SU5.ExoticCopyIndexBounds.net_constraints,
    ``GUT.SU5.ExoticCopyIndexBounds.positive_surpluses]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exotic index: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exotic index: {ds.length} strict transitive checks passed"
