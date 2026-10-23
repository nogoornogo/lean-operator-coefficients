import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorBridge

/-! Strict transitive checks of the basis-free arbitrary-multiplicity inverse. -/
open Lean in
run_cmd do
  let ds := [
    ``Physics.SixQuarkFlavorCoordinates.assemble,
    ``Physics.SixQuarkFlavorCoordinates.assemble_apply,
    ``Physics.SixQuarkFlavorCoordinates.assemble_invariant,
    ``Physics.SixQuarkFlavorCoordinates.coordinates_assemble,
    ``Physics.SixQuarkFlavorCoordinates.assemble_coordinates,
    ``Physics.SixQuarkTypedFlavor.homLinearEquiv,
    ``Physics.DeltaBTwoFlavorBridge.sectorCoefficientEquiv,
    ``Physics.DeltaBTwoFlavorBridge.sectorHomEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Arbitrary-flavor six-quark inverse {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Arbitrary-flavor six-quark inverse: {ds.length} strict transitive checks passed"
