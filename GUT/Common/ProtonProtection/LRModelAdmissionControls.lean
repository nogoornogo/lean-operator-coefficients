import GUT.Common.ProtonProtection.LRLightHiggs

/-! Countercontrols for the sufficiency of LR representation data. These
are quadratic-operator checks, not complete scalar-potential realizations. -/
namespace GUT.LRModelAdmissionControls
set_option autoImplicit false
noncomputable section
open LRLightHiggs

theorem both_unit_identity : quadratic 1 1 = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply PatiSalam.PhiRepresentation.equiv.symm.injective
  change PatiSalam.PhiRepresentation.split (quadratic 1 1 f) =
    PatiSalam.PhiRepresentation.split f
  rw [split_quadratic]
  simp

theorem both_unit_kernel : LinearMap.ker (quadratic 1 1) = ⊥ := by
  rw [both_unit_identity]
  exact LinearMap.ker_id

theorem both_zero : quadratic 0 0 = 0 := by
  apply LinearMap.ext
  intro f
  apply PatiSalam.PhiRepresentation.equiv.symm.injective
  change PatiSalam.PhiRepresentation.split (quadratic 0 0 f) =
    PatiSalam.PhiRepresentation.split 0
  rw [split_quadratic]
  simp [PatiSalam.PhiRepresentation.split]

theorem both_zero_kernel : LinearMap.ker (quadratic 0 0) = ⊤ := by
  rw [both_zero]
  exact LinearMap.ker_zero

/-- The identity control respects the entire declared LR bidoublet action. -/
theorem unit_full_lr_equivariant (g : LRGroup) (f : Phi) :
    quadratic 1 1 (bidoublet g f) = bidoublet g (quadratic 1 1 f) := by
  rw [both_unit_identity]
  rfl

theorem positive_selection : LinearMap.ker (quadratic 1 0) =
    LinearMap.range includeHiggs := kernel_eq_range 1 one_ne_zero

theorem unit_fails_selection : LinearMap.ker (quadratic 1 1) ≠
    LinearMap.range includeHiggs := by
  intro he
  let e : Two := Pi.single 0 1
  have hx : includeHiggs e ∈ LinearMap.ker (quadratic 1 1) := by
    rw [he]
    exact ⟨e,rfl⟩
  rw [both_unit_identity] at hx
  have hz : includeHiggs e = 0 := hx
  have hp := congrArg projectHiggs hz
  rw [project_include,map_zero] at hp
  have h0 := congrArg (fun v : Two => v 0) hp
  norm_num [e] at h0

/-- No universal unique-light-doublet conclusion follows even for SM-equivariant
quadratic operators with the prescribed residual action. -/
theorem selection_not_universal : ¬ ∀ M : Phi →ₗ[ℂ] Phi,
    (∀ g : StandardSMGaugeTensor.GaugeGroup, ∀ f,
      M (bidoublet (smEmbedding g) f) = bidoublet (smEmbedding g) (M f)) →
    LinearMap.ker M = LinearMap.range includeHiggs := by
  intro h
  exact unit_fails_selection (h (quadratic 1 1) (quadratic_equivariant 1 1))

end
end GUT.LRModelAdmissionControls
