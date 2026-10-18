import GUT.SU6.SelectionRules.Models.CyclicPatternSearch
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU6CyclicPatternSearch.qque, ``GUT.SU6CyclicPatternSearch.llhh,
    ``GUT.SU6CyclicPatternSearch.qque_simplify, ``GUT.SU6CyclicPatternSearch.witness,
    ``GUT.SU6CyclicPatternSearch.mixed_iff, ``GUT.SU6CyclicPatternSearch.package,
    ``GUT.SU6CyclicPatternSearch.character_line_iff,
    ``GUT.SU6CyclicPatternSearch.character_line_witness]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Cyclic search: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Cyclic search: {ds.length} strict transitive checks passed"
