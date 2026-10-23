import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkMatrix

/-! Compatibility presentations of the two literal source diagrams and their
selected words. Both matrices are derived from the source recipe and symbolic
extraction; no evaluated seed/basis/inverse table is supplied. -/
namespace Physics.HeeckLeSixQuarkCertificate
noncomputable section

abbrev rationalSeedCoordinates := HeeckLeSixQuarkRecipe.seed (K := ℚ)
abbrev selectedSeed := HeeckLeSixQuarkRecipe.selectedSeed
abbrev selectedWord := HeeckLeSixQuarkRecipe.selectedWord

def basisRational : Matrix (Fin 25) (Fin 25) ℚ := HeeckLeSixQuarkMatrix.basis

def inverseRational : Matrix (Fin 25) (Fin 25) ℚ := HeeckLeSixQuarkMatrix.inverse

theorem rational_left_inverse : inverseRational*basisRational = 1 :=
  HeeckLeSixQuarkMatrix.left_inverse

theorem rational_right_inverse : basisRational*inverseRational = 1 :=
  HeeckLeSixQuarkMatrix.right_inverse

def orbitR (j : Fin 25) : Fin 5 → Fin 5 → ℚ := HeeckLeSixQuarkRecipe.orbit j

def columnR (j : Fin 25) (p q : Fin 5) : ℚ :=
  basisRational ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25) (p,q)) j

theorem orbitR_agrees (i j : Fin 25) :
    orbitR j ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).1
      ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).2 = basisRational i j := rfl

end
end Physics.HeeckLeSixQuarkCertificate
