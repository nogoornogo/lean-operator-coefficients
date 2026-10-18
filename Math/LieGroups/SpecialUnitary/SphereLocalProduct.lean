import Math.LieGroups.SpecialUnitary.SphereSection

/-! Local product charts for the SU(n+1) last-column map, with actual
SU(n) fibers. These charts do not yet supply homotopy lifting or induction. -/

set_option autoImplicit false

namespace Math.SUN.SphereSection

noncomputable section

section LocalProduct

variable {n : ℕ} (U : Set (Sphere (n + 1)))
  (s : U → Block.Group (n + 1)) (hp : ∀ v, projection (s v) = v.val)

def localBase (g : projection ⁻¹' U) : U := ⟨projection g.val, g.property⟩

theorem localBase_continuous : Continuous (localBase U) :=
  continuous_induced_rng.mpr ((projection_continuous n).comp continuous_subtype_val)

def fiberCoordinate (g : projection ⁻¹' U) : VectorStabilizer.subgroup n :=
  ⟨(s (localBase U g))⁻¹ * g.val, difference_mem_stabilizer _ _ (hp (localBase U g))⟩

def reassemble (x : U × VectorStabilizer.subgroup n) : projection ⁻¹' U :=
  ⟨s x.1 * x.2.val, by
    change projection (s x.1 * x.2.val) ∈ U
    rw [projection_mul_stabilizer, hp]
    exact x.1.property⟩

theorem localBase_reassemble (x : U × VectorStabilizer.subgroup n) :
    localBase U (reassemble U s hp x) = x.1 := by
  apply Subtype.ext
  exact (projection_mul_stabilizer _ _).trans (hp x.1)

def stabilizerLocalProduct (hs : Continuous s) :
    (projection ⁻¹' U) ≃ₜ (U × VectorStabilizer.subgroup n) where
  toFun g := (localBase U g, fiberCoordinate U s hp g)
  invFun := reassemble U s hp
  left_inv g := by
    apply Subtype.ext
    change s (localBase U g) * ((s (localBase U g))⁻¹ * g.val) = g.val
    simp
  right_inv x := by
    apply Prod.ext
    · exact localBase_reassemble U s hp x
    · apply Subtype.ext
      change (s (localBase U (reassemble U s hp x)))⁻¹ * (s x.1 * x.2.val) = x.2.val
      rw [localBase_reassemble]
      simp
  continuous_toFun := by
    apply (localBase_continuous U).prodMk
    apply continuous_induced_rng.mpr
    exact ((hs.comp (localBase_continuous U)).inv).mul continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact (hs.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

def localProduct (hs : Continuous s) : (projection ⁻¹' U) ≃ₜ (U × Block.Group n) :=
  (stabilizerLocalProduct U s hp hs).trans
    (Homeomorph.prodCongr (Homeomorph.refl U) (VectorStabilizer.equiv n).toHomeomorph.symm)

theorem localProduct_fst (hs : Continuous s) (g : projection ⁻¹' U) :
    ((localProduct U s hp hs g).1).val = projection g.val := rfl

end LocalProduct

def northLocalProduct (n : ℕ) :
    (projection ⁻¹' patch (n + 1)) ≃ₜ (patch (n + 1) × Block.Group (n + 1)) :=
  localProduct _ specialSection projection_specialSection (specialSection_continuous n)

def southLocalProduct (n : ℕ) :
    (projection ⁻¹' southPatch (n + 1)) ≃ₜ (southPatch (n + 1) × Block.Group (n + 1)) :=
  localProduct _ southSection projection_southSection (southSection_continuous n)

/-- Local product neighborhoods cover the whole base, with the actual projection as first factor. -/
theorem exists_localProduct (n : ℕ) (v : Sphere (n + 2)) :
    ∃ U : Set (Sphere (n + 2)), IsOpen U ∧ v ∈ U ∧
      ∃ e : (projection ⁻¹' U) ≃ₜ (U × Block.Group (n + 1)),
        ∀ g, (e g).1.val = projection g.val := by
  rcases patches_cover v with hv | hv
  · exact ⟨patch (n + 1), patch_isOpen _, hv, northLocalProduct n,
      localProduct_fst _ _ _ _⟩
  · exact ⟨southPatch (n + 1), southPatch_isOpen _, hv, southLocalProduct n,
      localProduct_fst _ _ _ _⟩

end

end Math.SUN.SphereSection
