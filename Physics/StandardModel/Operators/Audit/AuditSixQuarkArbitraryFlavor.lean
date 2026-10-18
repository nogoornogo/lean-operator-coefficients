import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge

/-! Strict transitive checks of the basis-free arbitrary-multiplicity inverse. -/
open Lean in
run_cmd do
  let ds := [
    ``GUT.SixQuarkFlavorCoordinates.assemble,
    ``GUT.SixQuarkFlavorCoordinates.assemble_apply,
    ``GUT.SixQuarkFlavorCoordinates.assemble_invariant,
    ``GUT.SixQuarkFlavorCoordinates.coordinates_assemble,
    ``GUT.SixQuarkFlavorCoordinates.assemble_coordinates,
    ``GUT.SixQuarkTypedFlavor.homLinearEquiv,
    ``GUT.DeltaBTwoFlavorBridge.sectorCoefficientEquiv,
    ``GUT.DeltaBTwoFlavorBridge.sectorHomEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Arbitrary-flavor six-quark inverse {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Arbitrary-flavor six-quark inverse: {ds.length} strict transitive checks passed"
