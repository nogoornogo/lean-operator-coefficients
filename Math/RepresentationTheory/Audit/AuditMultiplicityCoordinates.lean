import Math.RepresentationTheory.MultiplicityCoordinates
import Math.RepresentationTheory.FiniteLocalBasisConversion
import Math.RepresentationTheory.StatisticsMultiplicityCoordinates
import Math.RepresentationTheory.FiniteLocalBasisConversionControls
import Math.RepresentationTheory.FiniteLocalIsotypicCompleteness
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.MultiplicityCoordinates.exists_block_coordinates,
    ``Math.MultiplicityCoordinates.action,
    ``Math.MultiplicityCoordinates.equiv,
    ``Math.MultiplicityCoordinates.conversion,
    ``Math.MultiplicityCoordinates.conversion_inverse,
    ``Math.MultiplicityCoordinates.coefficientEquiv,
    ``Math.MultiplicityCoordinates.coefficientEquiv_apply,
    ``Math.MultiplicityCoordinates.coefficientEquiv_inverse,
    ``Math.FiniteLocalBasisConversion.equiv,
    ``Math.FiniteLocalBasisConversion.equiv_apply,
    ``Math.FiniteLocalBasisConversion.inverse_apply,
    ``Math.FiniteLocalBasisConversion.reconstruction_agrees,
    ``Math.FiniteLocalBasisConversion.inverse_left,
    ``Math.FiniteLocalBasisConversion.inverse_right,
    ``Math.StatisticsMultiplicityCoordinates.chosen,
    ``Math.StatisticsMultiplicityCoordinates.coefficientEquiv,
    ``Math.StatisticsMultiplicityCoordinates.extraction,
    ``Math.StatisticsMultiplicityCoordinates.reconstruction,
    ``Math.StatisticsMultiplicityCoordinates.zero_iff,
    ``Math.StatisticsMultiplicityCoordinates.chosenCoefficientEquiv,
    ``Math.StatisticsMultiplicityCoordinates.change_apply,
    ``Math.StatisticsMultiplicityCoordinates.change_inverse,
    ``Math.FiniteLocalBasisConversionControls.normalized,
    ``Math.FiniteLocalBasisConversionControls.complete,
    ``Math.FiniteLocalBasisConversionControls.mixed_normalized,
    ``Math.FiniteLocalBasisConversionControls.mixed_complete,
    ``Math.FiniteLocalBasisConversionControls.forward_zero,
    ``Math.FiniteLocalBasisConversionControls.forward_one,
    ``Math.FiniteLocalBasisConversionControls.inverse_zero,
    ``Math.FiniteLocalBasisConversionControls.inverse_one,
    ``Math.FiniteLocalIsotypicCompleteness.characterMultiplicityEquiv]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Multiplicity coordinates: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Multiplicity coordinates: {declarations.length} strict transitive checks passed"
