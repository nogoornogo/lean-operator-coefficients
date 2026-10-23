import Math.RepresentationTheory.SU2.WeakDoubletScalars

/-! Algebraic duality of the actual SU2 doublet through its alternating form. -/
namespace Math.SU2DoubletDuality
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars

def epsilon : Doublet →ₗ[ℂ] Module.Dual ℂ Doublet where
  toFun v := v 0 • LinearMap.proj 1 - v 1 • LinearMap.proj 0
  map_add' v w := by ext x; simp [add_mul]; ring
  map_smul' z v := by ext x; simp [smul_eq_mul]; ring

@[simp] theorem epsilon_apply (v w : Doublet) : epsilon v w = v 0 * w 1 - v 1 * w 0 := rfl

theorem epsilon_invariant (g : Group) (v w : Doublet) :
    epsilon (doublet g v) (doublet g w) = epsilon v w := by
  have hd : Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := g.prop.2
  rw [Matrix.det_fin_two] at hd
  change (((g : Matrix (Fin 2) (Fin 2) ℂ).mulVec v) 0 *
      ((g : Matrix (Fin 2) (Fin 2) ℂ).mulVec w) 1 -
      ((g : Matrix (Fin 2) (Fin 2) ℂ).mulVec v) 1 *
      ((g : Matrix (Fin 2) (Fin 2) ℂ).mulVec w) 0) = _
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,epsilon_apply]
  linear_combination (v 0*w 1-v 1*w 0)*hd

theorem epsilon_injective : Function.Injective epsilon := by
  intro v w he
  have h0 := DFunLike.congr_fun he (Pi.single (1 : Fin 2) 1)
  have h1 := DFunLike.congr_fun he (Pi.single (0 : Fin 2) 1)
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

def equivalence : Representation.Equiv doublet doublet.dual where
  toLinearEquiv := LinearEquiv.ofBijective epsilon ⟨epsilon_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℂ) (V := Doublet)).symm).mp epsilon_injective⟩
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change epsilon (doublet g v) w = epsilon v (doublet g⁻¹ w)
    have he := epsilon_invariant g v (doublet g⁻¹ w)
    simpa only [Representation.self_inv_apply] using he

end
end Math.SU2DoubletDuality
