import Physics.StandardModel.Operators.SixQuarkInvariant
import Lean.Util.CollectAxioms

/-! Strict transitive axiom checks for the color-times-Weyl bridge. -/
run_cmd do
  let declarations := [
    ``GUT.SixWeylMultilinear.curried_apply,
    ``GUT.SixWeylMultilinear.exists_pairing_coordinates,
    ``GUT.SixWeylMultilinear.coordinates_reconstruct,
    ``GUT.SixWeylMultilinear.reconstruct_coordinates,
    ``GUT.SixWeylMultilinear.existsUnique_pairing_coordinates,
    ``GUT.SixQuarkInvariant.fixedSpin_invariant,
    ``GUT.SixQuarkInvariant.fixedColor_invariant,
    ``GUT.SixQuarkInvariant.spinCoordinates_invariant,
    ``GUT.SixQuarkInvariant.pure_ext,
    ``GUT.SixQuarkInvariant.exists_product_coordinates,
    ``GUT.SixQuarkInvariant.coordinates_formula,
    ``GUT.SixQuarkInvariant.eq_of_coordinates,
    ``GUT.SixQuarkInvariant.product_coordinates_unique,
    ``GUT.SixQuarkInvariant.orderedCoefficient_invariant,
    ``GUT.SixQuarkInvariant.exteriorRestriction_product_coordinates,
    ``GUT.SixQuarkInvariant.exteriorRestriction_speciesAlternating,
    ``GUT.SixQuarkInvariant.species_coordinate_constraint,
    ``GUT.SixQuarkInvariant.exterior_eq_of_coordinates]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-quark invariant bridge: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-quark invariant bridge: {declarations.length} strict transitive axiom checks passed"
