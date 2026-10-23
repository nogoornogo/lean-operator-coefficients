import Math.RepresentationTheory.Content.SixSlotSpeciesSum
import Math.LinearAlgebra.Selection.GrassmannCoefficient
import Lean.Util.CollectAxioms

/-! Strict transitive audits of species enumeration and Grassmann transport. -/
run_cmd do
  let declarations := [
    ``Math.SixSlotSpeciesSum.permutation_preserves,
    ``Math.SixSlotSpeciesSum.permutation_injective,
    ``Math.SixSlotSpeciesSum.permutation_surjective,
    ``Math.SixSlotSpeciesSum.permutation_sign,
    ``Math.SixSlotSpeciesSum.sum_preserving,
    ``Math.SixSlotSpeciesSum.alternating_slots_sum,
    ``Math.SixSlotSpeciesSum.alternating_slots_block,
    ``Math.GrassmannCoefficient.coordinateExpansion_eq,
    ``Math.GrassmannCoefficient.polynomial_generators,
    ``Math.GrassmannCoefficient.polynomial_pairing,
    ``Math.GrassmannCoefficient.polynomial_coordinate,
    ``Math.GrassmannCoefficient.pairingEquiv]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Species/Grassmann audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Species/Grassmann audit: {declarations.length} strict transitive checks passed"
