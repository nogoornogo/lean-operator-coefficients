import GUT.E6.Minuscule.SU5ExteriorCoordinates

open Math

/-!
# Concrete module-level comparison with the SU(5) generators

The target consists of actual scalar, defining, dual and exterior-power modules.
Only infinitesimal action comparison is asserted, not a group inclusion into E6.
-/

set_option autoImplicit false

namespace GUT.E6.Minuscule.SU5Coordinates

open Math.E6.Minuscule Math.E6
open GUT.SU5
open scoped Matrix

noncomputable section

abbrev Model := (Fin 2 → ℂ) × Matter.Five × (Fin 2 → Matter.BarFive) × Matter.Ten

def modelCoordinates : Model ≃ₗ[ℂ] (Index → ℂ) where
  toFun v a := match a with
    | .inl i => v.1 i
    | .inr (.inl i) => v.2.1 i
    | .inr (.inr (.inl (k, i))) => UnitaryMatter.barFiveBasis.equivFun (v.2.2.1 k) i
    | .inr (.inr (.inr p)) => exteriorBasis.equivFun v.2.2.2 p
  invFun c := (fun i => c (.inl i), fun i => c (.inr (.inl i)),
    fun k => UnitaryMatter.barFiveBasis.equivFun.symm (fun i => c (.inr (.inr (.inl (k, i))))),
    exteriorBasis.equivFun.symm (fun p => c (.inr (.inr (.inr p)))))
  left_inv v := by
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
    · funext k
      exact UnitaryMatter.barFiveBasis.equivFun.symm_apply_apply _
    · exact exteriorBasis.equivFun.symm_apply_apply _
  right_inv c := by
    funext a
    rcases a with a | a | ⟨k, a⟩ | a
    · rfl
    · rfl
    · exact congrFun (UnitaryMatter.barFiveBasis.equivFun.apply_symm_apply _) a
    · exact congrFun (exteriorBasis.equivFun.apply_symm_apply _) a
  map_add' v w := by
    funext a
    rcases a with a | a | ⟨k, a⟩ | a <;> simp [map_add]
  map_smul' z v := by
    funext a
    rcases a with a | a | ⟨k, a⟩ | a <;> simp

def modelInfinitesimal (X : Matrix (Fin 5) (Fin 5) ℂ) : Module.End ℂ Model where
  toFun v := (0, Matrix.toLin' X v.2.1, fun k => dualInfinitesimal X (v.2.2.1 k),
    exteriorInfinitesimal X v.2.2.2)
  map_add' v w := by
    simp
    exact ⟨Matrix.mulVec_add _ _ _, rfl⟩
  map_smul' z v := by
    simp
    rfl

theorem modelInfinitesimal_coordinates (X : Matrix (Fin 5) (Fin 5) ℂ) (v : Model) :
    modelCoordinates (modelInfinitesimal X v) = blockMatrix X *ᵥ modelCoordinates v := by
  funext a
  rcases a with a | a | ⟨k, a⟩ | a
  · simp [modelCoordinates, modelInfinitesimal, Matrix.mulVec, dotProduct, blockMatrix]
  · simp [modelCoordinates, modelInfinitesimal, Matrix.mulVec, dotProduct, blockMatrix,
      Fintype.sum_sum_type, Matrix.toLin'_apply]
  · have h := congrFun (LinearMap.toMatrix_mulVec_repr UnitaryMatter.barFiveBasis
      UnitaryMatter.barFiveBasis (dualInfinitesimal X) (v.2.2.1 k)) a
    rw [dualInfinitesimal_matrix] at h
    simpa [modelCoordinates, modelInfinitesimal, Matrix.mulVec, dotProduct, blockMatrix,
      Fintype.sum_sum_type, Fintype.sum_prod_type, Module.Basis.equivFun_apply] using h.symm
  · have h := congrFun (LinearMap.toMatrix_mulVec_repr exteriorBasis exteriorBasis
      (exteriorInfinitesimal X) v.2.2.2) a
    rw [exteriorInfinitesimal_matrix] at h
    simpa [modelCoordinates, modelInfinitesimal, Matrix.mulVec, dotProduct, blockMatrix,
      Fintype.sum_sum_type, Module.Basis.equivFun_apply] using h.symm

/-- The signed coordinate map now lands in the actual direct sum of modules. -/
def actualModelEquiv : (Fin 27 → ℂ) ≃ₗ[ℂ] Model :=
  signedCoordinates.trans modelCoordinates.symm

theorem actual_generator_comparison (k : Fin 3) (i : Fin 4) (v : Fin 27 → ℂ) :
    actualModelEquiv (complexGenerator k i *ᵥ v) =
      modelInfinitesimal ((fundamentalGenerator k i).map (Int.castRingHom ℂ))
        (actualModelEquiv v) := by
  apply modelCoordinates.injective
  rw [modelInfinitesimal_coordinates]
  simpa [actualModelEquiv] using generator_intertwining k i v

theorem actualModelEquiv_hermitian (x y : Fin 27 → ℂ) :
    (∑ a : Index, star (modelCoordinates (actualModelEquiv x) a) *
      modelCoordinates (actualModelEquiv y) a) =
      ∑ j : Fin 27, star (x j) * y j := by
  simpa [actualModelEquiv] using signedCoordinates_hermitian x y

def modelGenerator (k : Fin 3) (i : Fin 4) : Module.End ℂ Model :=
  modelInfinitesimal ((fundamentalGenerator k i).map (Int.castRingHom ℂ))

theorem actual_compactX_comparison (i : Fin 4) (v : Fin 27 → ℂ) :
    actualModelEquiv (compactX (node i) *ᵥ v) =
      (modelGenerator 0 i - modelGenerator 1 i) (actualModelEquiv v) := by
  have he := actual_generator_comparison 0 i v
  have hf := actual_generator_comparison 1 i v
  change actualModelEquiv (raising (node i) *ᵥ v) = _ at he
  change actualModelEquiv (lowering (node i) *ᵥ v) = _ at hf
  rw [compactX, Matrix.sub_mulVec, map_sub actualModelEquiv, he, hf]
  rfl

theorem actual_compactY_comparison (i : Fin 4) (v : Fin 27 → ℂ) :
    actualModelEquiv (compactY (node i) *ᵥ v) =
      (Complex.I • (modelGenerator 0 i + modelGenerator 1 i)) (actualModelEquiv v) := by
  have he := actual_generator_comparison 0 i v
  have hf := actual_generator_comparison 1 i v
  change actualModelEquiv (raising (node i) *ᵥ v) = _ at he
  change actualModelEquiv (lowering (node i) *ᵥ v) = _ at hf
  rw [compactY, Matrix.smul_mulVec, Matrix.add_mulVec, map_smul, map_add, he, hf]
  rfl

theorem actual_compactH_comparison (i : Fin 4) (v : Fin 27 → ℂ) :
    actualModelEquiv (compactH (node i) *ᵥ v) =
      (Complex.I • modelGenerator 2 i) (actualModelEquiv v) := by
  have hh := actual_generator_comparison 2 i v
  change actualModelEquiv (cartan (node i) *ᵥ v) = _ at hh
  rw [compactH, Matrix.smul_mulVec, map_smul, hh]
  rfl

end

end GUT.E6.Minuscule.SU5Coordinates
