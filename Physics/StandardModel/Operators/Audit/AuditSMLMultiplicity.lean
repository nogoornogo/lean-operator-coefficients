import Physics.StandardModel.Operators.SMLConjugateMultiplicity
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Lepton counting audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMLWeightExpansion.source_character,
    ``GUT.SMLWeightExpansion.torus_character,
    ``GUT.SMLContinuousCharacter.field_basis_coordinates,
    ``GUT.SMLContinuousCharacter.field_continuous,
    ``GUT.SMLContinuousCharacter.source_continuous,
    ``GUT.SMLContinuousCharacter.equiv,
    ``GUT.SMLContinuousCharacter.continuous_model,
    ``GUT.SMLContinuousCharacter.coefficient_dimension,
    ``GUT.SMLKernelDimension.source_color_fixed,
    ``GUT.SMLKernelDimension.action_hyper_fixed,
    ``GUT.SMLKernelDimension.coefficientEquiv,
    ``GUT.SMLKernelDimension.kernel_dimension,
    ``GUT.SMLKernelDimension.rank_add_multiplicity,
    ``GUT.SMLKernelDimension.allowed_iff,
    ``GUT.SMLKernelDimension.multiplicity_llhh,
    ``GUT.SMLKernelDimension.multiplicity_odd,
    ``GUT.SMLKernelDimension.multiplicity_above_capacity,
    ``GUT.SMLConjugateMultiplicity.fieldEquiv,
    ``GUT.SMLConjugateMultiplicity.sourceEquiv,
    ``GUT.SMLConjugateMultiplicity.bosonEquiv,
    ``GUT.SMLConjugateMultiplicity.coefficientEquiv,
    ``GUT.SMLConjugateMultiplicity.allowed_iff,
    ``GUT.SMLConjugateMultiplicity.kernel_dimension]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Lepton counting: layer and {ds.length} strict transitive checks passed"
