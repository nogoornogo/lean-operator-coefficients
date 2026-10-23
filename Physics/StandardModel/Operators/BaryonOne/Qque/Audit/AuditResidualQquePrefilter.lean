import Physics.StandardModel.Operators.BaryonOne.Qque.ResidualQquePrefilter
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``Physics.ResidualQquePrefilter.Triplet.rightUpEquiv,
    ``Physics.ResidualQquePrefilter.Triplet.rightElectronEquiv,
    ``Physics.ResidualQquePrefilter.Triplet.neutral_hasCoefficient,
    ``Physics.ResidualQquePrefilter.necessary,
    ``Physics.ResidualQquePrefilter.neutral_excludes,
    ``Physics.ResidualQquePrefilter.equal_species_excludes,
    ``Physics.ResidualQquePrefilter.block_excludes,
    ``Physics.ResidualQquePrefilter.chargedMap,
    ``Physics.ResidualQquePrefilter.selectedTriplet,
    ``Physics.ResidualQquePrefilter.selected_neutral_reject,
    ``Physics.ResidualQquePrefilter.preserve,
    ``Physics.ResidualQquePrefilter.reject,
    ``Physics.ResidualQquePrefilter.selected_preserve,
    ``Physics.ResidualQquePrefilter.finite_preserve]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Residual qque prefilter: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Residual qque prefilter: {ds.length} strict transitive checks passed"
