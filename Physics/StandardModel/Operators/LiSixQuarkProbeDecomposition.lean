import Physics.StandardModel.Operators.LiSixQuarkExtension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The separating probe splits off the extra local component without the
25-by-25 basis or inverse tables. This does not assert that printed orbits
span its kernel: that is a separate, stronger obligation. -/
namespace GUT.LiSixQuarkExtension
noncomputable section

abbrev LocalArray := Fin 5 → Fin 5 → ℂ

/-- Remove precisely the component measured by the normalized probe. -/
def withoutExtra (c : LocalArray) : LocalArray := c - extraProbe c • extra

theorem withoutExtra_mem_kernel (c : LocalArray) :
    withoutExtra c ∈ LinearMap.ker extraProbeLinear := by
  change extraProbeLinear (c - extraProbe c • extra) = 0
  rw [map_sub, map_smul]
  change extraProbe c - extraProbe c • extraProbe extra = 0
  rw [extraProbe_extra, smul_eq_mul, mul_one, sub_self]

theorem reconstruct_withoutExtra (c : LocalArray) :
    withoutExtra c + extraProbe c • extra = c := sub_add_cancel _ _

/-- The probe fixes the coefficient of the added line; subtraction fixes
its kernel component. No independence test of a numerical matrix is needed. -/
theorem decomposition_unique (c k : LocalArray) (z : ℂ)
    (hk : k ∈ LinearMap.ker extraProbeLinear) (h : k + z • extra = c) :
    k = withoutExtra c ∧ z = extraProbe c := by
  have hz : z = extraProbe c := by
    have hp := congrArg extraProbeLinear h
    rw [map_add, map_smul] at hp
    change extraProbeLinear k + z • extraProbe extra = extraProbe c at hp
    rw [show extraProbeLinear k = 0 from hk, extraProbe_extra,
      smul_eq_mul, mul_one, zero_add] at hp
    exact hp
  refine ⟨?_, hz⟩
  unfold withoutExtra
  rw [← hz, ← h, add_sub_cancel_right]

/-- Human-readable coordinates: a vector in the probe kernel and one scalar. -/
def probeDecomposition : LocalArray ≃ₗ[ℂ]
    (LinearMap.ker extraProbeLinear) × ℂ where
  toFun c := (⟨withoutExtra c, withoutExtra_mem_kernel c⟩, extraProbe c)
  invFun v := v.1.1 + v.2 • extra
  left_inv := reconstruct_withoutExtra
  right_inv v := by
    obtain ⟨hk, hz⟩ := decomposition_unique (v.1.1 + v.2 • extra)
      v.1.1 v.2 v.1.2 rfl
    apply Prod.ext
    · exact Subtype.ext hk.symm
    · exact hz.symm
  map_add' c d := by
    apply Prod.ext
    · apply Subtype.ext
      change c + d - extraProbe (c + d) • extra =
        (c - extraProbe c • extra) + (d - extraProbe d • extra)
      rw [show extraProbe (c + d) = extraProbe c + extraProbe d from
        extraProbeLinear.map_add c d, add_smul]
      abel
    · exact extraProbeLinear.map_add c d
  map_smul' z c := by
    apply Prod.ext
    · apply Subtype.ext
      change z • c - extraProbe (z • c) • extra =
        z • (c - extraProbe c • extra)
      rw [show extraProbe (z • c) = z * extraProbe c from
        extraProbeLinear.map_smul z c, smul_sub, smul_smul]
    · exact extraProbeLinear.map_smul z c

/-- The hyperplane has dimension 24 independently of any printed-orbit basis. -/
theorem probe_kernel_finrank : Module.finrank ℂ (LinearMap.ker extraProbeLinear) = 24 := by
  have hs : Function.Surjective extraProbeLinear := by
    intro z
    refine ⟨z • extra, ?_⟩
    rw [map_smul]
    change z • extraProbe extra = z
    rw [extraProbe_extra, smul_eq_mul, mul_one]
  have h := extraProbeLinear.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self] at h
  have hd : Module.finrank ℂ LocalArray = 25 := by
    simp [LocalArray, Module.finrank_pi_fintype]
  change 1 + Module.finrank ℂ (LinearMap.ker extraProbeLinear) =
    Module.finrank ℂ LocalArray at h
  rw [hd] at h
  omega

end
end GUT.LiSixQuarkExtension
