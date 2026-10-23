import Physics.FieldTheory.Mass.Spectrum.ChiralActionConvention
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Chiral action convention imports model {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.ChiralActionConvention.dirac_bar_product,
    ``Physics.ChiralActionConvention.majorana_bar_right,
    ``Physics.ChiralActionConvention.right_conj_inverse,
    ``Physics.ChiralActionConvention.barred_lr,
    ``Physics.ChiralActionConvention.conjugate_vertex,
    ``Physics.ChiralActionConvention.kinetic_mod_derivative,
    ``Physics.ChiralActionConvention.kinetic_matrix_mod_derivative,
    ``Physics.ChiralActionConvention.majorana_kinetic,
    ``Physics.ChiralActionConvention.flip_time,
    ``Physics.ChiralActionConvention.flip_space,
    ``Physics.ChiralActionConvention.canonical_norm_form]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Chiral action convention {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Chiral action convention: layer and {ds.length} strict transitive checks passed"
