import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalCoordinates

open Math
open scoped TensorProduct
namespace Physics.DeltaBTwoContractionRelations
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem fierz_blockAlternation
    (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :
    blockAlternation valueO2 u d - blockAlternation valueO1 u d =
      3 * blockAlternation valueO3 u d := by
  let v : Fin 6 → SixQuarkInvariant.Quark :=
    ![(u 0).1 ⊗ₜ[ℂ] (u 0).2, (d 0).1 ⊗ₜ[ℂ] (d 0).2,
      (u 1).1 ⊗ₜ[ℂ] (u 1).2, (d 1).1 ⊗ₜ[ℂ] (d 1).2,
      (d 2).1 ⊗ₜ[ℂ] (d 2).2, (d 3).1 ⊗ₜ[ℂ] (d 3).2]
  have he := congrArg
    (fun f : SixQuarkTwoCoordinates.Sector => SixQuarkInvariant.exteriorRestriction f.1 v)
    SixQuarkConventionalCoordinates.fierz
  simp only [SixQuarkInvariant.exteriorRestriction_apply] at he
  change SixQuarkInvariant.exteriorRestriction SixQuarkConventionalBasis.O2.1 v -
    SixQuarkInvariant.exteriorRestriction SixQuarkConventionalBasis.O1.1 v =
    3 * SixQuarkInvariant.exteriorRestriction SixQuarkConventionalBasis.O3.1 v at he
  simpa only [v, SixQuarkConventionalCoordinates.O2_block,
    SixQuarkConventionalCoordinates.O1_block,
    SixQuarkConventionalCoordinates.O3_block] using he

end
end Physics.DeltaBTwoContractionRelations
