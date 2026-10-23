import Math.RepresentationTheory.Characters.FiniteTorusPresentation
import Math.RepresentationTheory.Constructions.BasisActionContinuity
import Math.RepresentationTheory.Coefficients.ProductInvariantCoefficients
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Finite torus presentation audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ProductInvariantCoefficients.fixed_iff, ``Math.ProductInvariantCoefficients.equiv,
    ``Math.BasisActionContinuity.copy_continuous, ``Math.BasisActionContinuity.trivial,
    ``Math.BasisActionContinuity.tensor, ``Math.BasisActionContinuity.dual,
    ``Math.BasisActionContinuity.comp, ``Math.BasisActionContinuity.source_copy_continuous,
    ``Math.FiniteTorusPresentation.active_continuous, ``Math.FiniteTorusPresentation.activeCharacter,
    ``Math.FiniteTorusPresentation.weight, ``Math.FiniteTorusPresentation.weight_character,
    ``Math.FiniteTorusPresentation.coefficients, ``Math.FiniteTorusPresentation.presentation,
    ``Math.FiniteTorusPresentation.inverseTorus, ``Math.FiniteTorusPresentation.inverse_coordinates,
    ``Math.FiniteTorusPresentation.inverseModel_unitary, ``Math.FiniteTorusPresentation.inverseModel_continuous,
    ``Math.FiniteTorusPresentation.inverseCoefficients, ``Math.FiniteTorusPresentation.inverse_presentation]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Finite torus presentation audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Finite torus presentation audit: layer and {ds.length} strict transitive checks passed"
