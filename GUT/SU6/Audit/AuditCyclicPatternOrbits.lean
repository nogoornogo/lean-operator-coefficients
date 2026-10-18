import GUT.SU6.SelectionRules.Models.CyclicPatternOrbits
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU6CyclicPatternOrbits.charge_rescaling,
    ``GUT.SU6CyclicPatternOrbits.tests_invariant,
    ``GUT.SU6CyclicPatternOrbits.normalized_charge,
    ``GUT.SU6CyclicPatternOrbits.hypercharge_dressing,
    ``GUT.SU6CyclicPatternOrbits.scalar_block_neutral,
    ``GUT.SU6CyclicPatternOrbits.no_scalar_block_fit]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Cyclic orbits: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Cyclic orbits: {ds.length} strict transitive checks passed"
