import Physics.StandardModel.Operators.ResidualQquePrefilter
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.ResidualQquePrefilter.Triplet.rightUpEquiv,
    ``GUT.ResidualQquePrefilter.Triplet.rightElectronEquiv,
    ``GUT.ResidualQquePrefilter.Triplet.neutral_hasCoefficient,
    ``GUT.ResidualQquePrefilter.necessary,
    ``GUT.ResidualQquePrefilter.neutral_excludes,
    ``GUT.ResidualQquePrefilter.equal_species_excludes,
    ``GUT.ResidualQquePrefilter.block_excludes,
    ``GUT.ResidualQquePrefilter.chargedMap,
    ``GUT.ResidualQquePrefilter.selectedTriplet,
    ``GUT.ResidualQquePrefilter.selected_neutral_reject,
    ``GUT.ResidualQquePrefilter.preserve,
    ``GUT.ResidualQquePrefilter.reject,
    ``GUT.ResidualQquePrefilter.selected_preserve,
    ``GUT.ResidualQquePrefilter.finite_preserve]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Residual qque prefilter: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Residual qque prefilter: {ds.length} strict transitive checks passed"
