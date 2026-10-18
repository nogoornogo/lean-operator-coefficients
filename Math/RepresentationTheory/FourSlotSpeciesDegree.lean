import Math.RepresentationTheory.FourSlotAlternation

/-! An intrinsic species-degree (2,1,1) subspace of exterior coefficients.
Independent scaling of each summand defines the sector without an assembly image. -/
namespace Math.FourSlotSpeciesDegree
noncomputable section
open Representation FourSlotAlternation
open scoped TensorProduct

variable {H A B C : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (c : Representation ℂ H C)

def scaling (r s t : ℂ) : IntertwiningMap (action a b c) (action a b c) where
  toLinearMap :=
    { toFun := fun v => (r • v.1, s • v.2.1, t • v.2.2)
      map_add' := by intro v w; simp [smul_add]
      map_smul' := by intro z v; simp [smul_smul, mul_comm] }
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    change (r • a h v.1, s • b h v.2.1, t • c h v.2.2) =
      (a h (r • v.1), b h (s • v.2.1), c h (t • v.2.2))
    simp only [map_smul]

abbrev coefficients := IntertwiningMap ((action a b c).exteriorPower 4)
  (Representation.trivial ℂ H ℂ)

def HasDegree (f : coefficients a b c) : Prop :=
  ∀ (r s t : ℂ) v, f ((scaling a b c r s t).exteriorPower 4 v) =
    (r * r * s * t) • f v

def sector : Submodule ℂ (coefficients a b c) where
  carrier := {f | HasDegree a b c f}
  zero_mem' := by intro r s t v; simp
  add_mem' := by
    intro f g hf hg r s t v
    change f _ + g _ = _ • (f v + g v)
    rw [hf r s t v, hg r s t v, smul_add]
  smul_mem' := by
    intro z f hf r s t v
    change z • f _ = _ • (z • f v)
    rw [hf r s t v, smul_comm z]

theorem coefficient_hasDegree
    (f : IntertwiningMap ((a.tprod a).tprod (b.tprod c)) (Representation.trivial ℂ H ℂ)) :
    HasDegree a b c (coefficient a b c f) := by
  intro r s t
  suffices h : (coefficient a b c f).toLinearMap.comp
      ((scaling a b c r s t).exteriorPower 4).toLinearMap =
      (r * r * s * t) • (coefficient a b c f).toLinearMap by
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
  change Equiv.Perm.sign p • f (((r • (v (p 0)).1) ⊗ₜ[ℂ] (r • (v (p 1)).1)) ⊗ₜ[ℂ]
      ((s • (v (p 2)).2.1) ⊗ₜ[ℂ] (t • (v (p 3)).2.2))) =
    (r * r * s * t) • (Equiv.Perm.sign p • f
      (((v (p 0)).1 ⊗ₜ[ℂ] (v (p 1)).1) ⊗ₜ[ℂ]
        ((v (p 2)).2.1 ⊗ₜ[ℂ] (v (p 3)).2.2)))
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul, smul_smul]
  simp [smul_eq_mul, mul_smul_comm, mul_assoc, mul_comm, mul_left_comm]

end
end Math.FourSlotSpeciesDegree
