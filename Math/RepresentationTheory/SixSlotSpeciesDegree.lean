import Math.RepresentationTheory.SixSlotAlternation

/-! Intrinsic degree `(2,4)` coefficients on the exterior power of `A ⊕ B`. -/
namespace Math.SixSlotSpeciesDegree

set_option autoImplicit false
noncomputable section

open Representation SixSlotAlternation

variable {H A B : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B)

/-- Independent scalar multiplication on the two species summands. -/
def scaling (r s : ℂ) : IntertwiningMap (action a b) (action a b) where
  toLinearMap :=
    { toFun := fun v => (r • v.1, s • v.2)
      map_add' := by intro v w; simp [smul_add]
      map_smul' := by intro z v; simp [smul_smul, mul_comm] }
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    change (r • a h v.1, s • b h v.2) =
      (a h (r • v.1), b h (s • v.2))
    simp only [map_smul]

abbrev coefficients := IntertwiningMap ((action a b).exteriorPower 6)
  (Representation.trivial ℂ H ℂ)

/-- The intrinsic bidegree `(2,4)` condition, independent of an ordered
contraction ansatz. -/
def HasDegree (f : coefficients a b) : Prop :=
  ∀ (r s : ℂ) v, f ((scaling a b r s).exteriorPower 6 v) =
    (r * r * s * s * s * s) • f v

def sector : Submodule ℂ (coefficients a b) where
  carrier := {f | HasDegree a b f}
  zero_mem' := by intro r s v; simp
  add_mem' := by
    intro f g hf hg r s v
    change f _ + g _ = _ • (f v + g v)
    rw [hf r s v, hg r s v, smul_add]
  smul_mem' := by
    intro z f hf r s v
    change z • f _ = _ • (z • f v)
    rw [hf r s v, smul_comm z]

theorem coefficient_hasDegree
    (f : IntertwiningMap (orderedRepresentation a b)
      (Representation.trivial ℂ H ℂ)) :
    HasDegree a b (coefficient a b f) := by
  intro r s
  suffices h : (coefficient a b f).toLinearMap.comp
      ((scaling a b r s).exteriorPower 6).toLinearMap =
      (r * r * s * s * s * s) • (coefficient a b f).toLinearMap by
    intro v
    exact LinearMap.congr_fun h v
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    IntertwiningMap.exteriorPower_toLinearMap, exteriorPower.map_apply_ιMulti,
    coefficient, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    LinearMap.smul_apply, alternating, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  change Equiv.Perm.sign p • f ((((r • (v (p 0)).1) ⊗ₜ[ℂ] (s • (v (p 1)).2)) ⊗ₜ[ℂ]
      ((r • (v (p 2)).1) ⊗ₜ[ℂ] (s • (v (p 3)).2))) ⊗ₜ[ℂ]
        ((s • (v (p 4)).2) ⊗ₜ[ℂ] (s • (v (p 5)).2))) =
    (r * r * s * s * s * s) • (Equiv.Perm.sign p •
      f (((v (p 0)).1 ⊗ₜ[ℂ] (v (p 1)).2) ⊗ₜ[ℂ]
        ((v (p 2)).1 ⊗ₜ[ℂ] (v (p 3)).2) ⊗ₜ[ℂ]
          ((v (p 4)).2 ⊗ₜ[ℂ] (v (p 5)).2)))
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul, smul_smul]
  simp [smul_eq_mul, mul_smul_comm, mul_assoc, mul_comm, mul_left_comm]

end
end Math.SixSlotSpeciesDegree
