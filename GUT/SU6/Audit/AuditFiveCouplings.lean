import GUT.SU6.Yukawa.FiveCouplings
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.SU6FiveCouplings.flavor,
    ``GUT.SU6FiveCouplings.coupling, ``GUT.SU6FiveCouplings.mass,
    ``GUT.SU6FiveCouplings.mass_fiveForm, ``GUT.SU6FiveCouplings.base_coordinates,
    ``GUT.SU6FiveCouplings.projected_coordinates_of, ``GUT.SU6FiveCouplings.mass_formula_of,
    ``GUT.SU6FiveCouplings.mass_formula, ``GUT.SU6FiveCouplings.dualProbe_apply,
    ``GUT.SU6FiveCouplings.exteriorProbe_contract, ``GUT.SU6FiveCouplings.probe_values_of,
    ``GUT.SU6FiveCouplings.probe_values,
    ``GUT.SU6FiveCouplings.mass_eq_iff, ``GUT.SU6FiveCouplings.coupling_eq_iff,
    ``GUT.SU6FiveCouplings.massMap, ``GUT.SU6FiveCouplings.massMap_injective,
    ``GUT.SU6FiveCouplings.massMap_range_finrank, ``GUT.SU6FiveCouplings.mass_form_zero_iff,
    ``GUT.SU6FiveCouplings.range_realized]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Five SU6 Yukawa couplings: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Five SU6 Yukawa couplings: {declarations.length} strict axiom checks passed"
