import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkInvariant
import Lean.Util.CollectAxioms

/-! Strict transitive axiom checks for the color-times-Weyl bridge. -/
run_cmd do
  let declarations := [
    ``Physics.SixWeylMultilinear.curried_apply,
    ``Physics.SixWeylMultilinear.exists_pairing_coordinates,
    ``Physics.SixWeylMultilinear.coordinates_reconstruct,
    ``Physics.SixWeylMultilinear.reconstruct_coordinates,
    ``Physics.SixWeylMultilinear.existsUnique_pairing_coordinates,
    ``Physics.SixQuarkInvariant.fixedSpin_invariant,
    ``Physics.SixQuarkInvariant.fixedColor_invariant,
    ``Physics.SixQuarkInvariant.spinCoordinates_invariant,
    ``Physics.SixQuarkInvariant.pure_ext,
    ``Physics.SixQuarkInvariant.exists_product_coordinates,
    ``Physics.SixQuarkInvariant.coordinates_formula,
    ``Physics.SixQuarkInvariant.eq_of_coordinates,
    ``Physics.SixQuarkInvariant.product_coordinates_unique,
    ``Physics.SixQuarkInvariant.orderedCoefficient_invariant,
    ``Physics.SixQuarkInvariant.exteriorRestriction_product_coordinates,
    ``Physics.SixQuarkInvariant.exteriorRestriction_speciesAlternating,
    ``Physics.SixQuarkInvariant.species_coordinate_constraint,
    ``Physics.SixQuarkInvariant.exterior_eq_of_coordinates]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-quark invariant bridge: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-quark invariant bridge: {declarations.length} strict transitive axiom checks passed"
