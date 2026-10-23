import Physics.StandardModel.Operators.Support.Lepton.SMLConjugateMultiplicity
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Lepton counting audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMLWeightExpansion.source_character,
    ``Physics.SMLWeightExpansion.torus_character,
    ``Physics.SMLContinuousCharacter.field_basis_coordinates,
    ``Physics.SMLContinuousCharacter.field_continuous,
    ``Physics.SMLContinuousCharacter.source_continuous,
    ``Physics.SMLContinuousCharacter.equiv,
    ``Physics.SMLContinuousCharacter.continuous_model,
    ``Physics.SMLContinuousCharacter.coefficient_dimension,
    ``Physics.SMLKernelDimension.source_color_fixed,
    ``Physics.SMLKernelDimension.action_hyper_fixed,
    ``Physics.SMLKernelDimension.coefficientEquiv,
    ``Physics.SMLKernelDimension.kernel_dimension,
    ``Physics.SMLKernelDimension.rank_add_multiplicity,
    ``Physics.SMLKernelDimension.allowed_iff,
    ``Physics.SMLKernelDimension.multiplicity_llhh,
    ``Physics.SMLKernelDimension.multiplicity_odd,
    ``Physics.SMLKernelDimension.multiplicity_above_capacity,
    ``Physics.SMLConjugateMultiplicity.fieldEquiv,
    ``Physics.SMLConjugateMultiplicity.sourceEquiv,
    ``Physics.SMLConjugateMultiplicity.bosonEquiv,
    ``Physics.SMLConjugateMultiplicity.coefficientEquiv,
    ``Physics.SMLConjugateMultiplicity.allowed_iff,
    ``Physics.SMLConjugateMultiplicity.kernel_dimension]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Lepton counting: layer and {ds.length} strict transitive checks passed"
