import Physics.FieldTheory.Mass.ChiralActionConvention
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Chiral action convention imports model {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.ChiralActionConvention.dirac_bar_product,
    ``GUT.ChiralActionConvention.majorana_bar_right,
    ``GUT.ChiralActionConvention.right_conj_inverse,
    ``GUT.ChiralActionConvention.barred_lr,
    ``GUT.ChiralActionConvention.conjugate_vertex,
    ``GUT.ChiralActionConvention.kinetic_mod_derivative,
    ``GUT.ChiralActionConvention.kinetic_matrix_mod_derivative,
    ``GUT.ChiralActionConvention.majorana_kinetic,
    ``GUT.ChiralActionConvention.flip_time,
    ``GUT.ChiralActionConvention.flip_space,
    ``GUT.ChiralActionConvention.canonical_norm_form]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Chiral action convention {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Chiral action convention: layer and {ds.length} strict transitive checks passed"
