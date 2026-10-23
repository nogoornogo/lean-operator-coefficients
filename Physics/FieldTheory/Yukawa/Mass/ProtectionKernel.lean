import Physics.FieldTheory.Yukawa.Mass.VacuumMassProtection
import Physics.FieldTheory.Yukawa.Mass.YukawaClassification
import Physics.FieldTheory.Mass.Algebra.ExactRadical

/-! Linear UV families give a kernel, or a translated kernel when bare mixing is present. -/
set_option autoImplicit false
namespace Physics.YukawaProtectionKernel
noncomputable section
open Representation InvariantWeylMass InvariantMassProtection WeylYukawaMass

variable {G K S V W P : Type*} [Group G] [Group K]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]
  {rhoS : Representation ℂ G S} {rho : Representation ℂ G V}
  {sigma : Representation ℂ G W}
  (J : P →ₗ[ℂ] IntertwiningMap rhoS (SymmetricScalarYukawa.scalarRho (rho.prod sigma)))

def family (p : P) : EquivariantYukawa rhoS (rho.prod sigma) :=
  YukawaClassification.ofMap rhoS (rho.prod sigma) (J p)

variable (f : K →* G) (v : S) (B : SymmetricMass (rho.comp f))

def obstruction : P →ₗ[ℂ] (B.radical.toSubmodule →ₗ[ℂ] Module.Dual ℂ W) where
  toFun p := (((J p v).val.compl₁₂ (LinearMap.inl ℂ V W)
    (LinearMap.inr ℂ V W)).comp B.radical.toSubmodule.subtype)
  map_add' p q := by ext x w; simp
  map_smul' a p := by ext x w; simp

variable (bare : SymmetricMass (rho.prod sigma))

def offset : B.radical.toSubmodule →ₗ[ℂ] Module.Dual ℂ W :=
  (bare.form.compl₁₂ (LinearMap.inl ℂ V W) (LinearMap.inr ℂ V W)).comp
    B.radical.toSubmodule.subtype

variable (hv : ∀ k, rhoS (f k) v = v)

theorem protected_iff (p : P)
    (he : Extends B (VacuumMassProtection.mass bare (family J) f v hv p)) :
    Preserves B (VacuumMassProtection.mass bare (family J) f v hv p) ↔
      obstruction J f v B p = -offset f B bare := by
  rw [VacuumMassProtection.preserves_iff bare (family J) f v hv B p he]
  constructor
  · intro h
    ext x w
    change (J p v).val (x.val, 0) (0, w) = -bare.form (x.val, 0) (0, w)
    have hh := h x w
    change bare.form (x.val, 0) (0, w) + (J p v).val (x.val, 0) (0, w) = 0 at hh
    exact eq_neg_of_add_eq_zero_right hh
  · intro h x w
    have hh := LinearMap.congr_fun (congrArg (fun C => C x) h) w
    change (J p v).val (x.val, 0) (0, w) = -bare.form (x.val, 0) (0, w) at hh
    change bare.form (x.val, 0) (0, w) + (J p v).val (x.val, 0) (0, w) = 0
    rw [hh, add_neg_cancel]

theorem protected_iff_mem_kernel (p : P)
    (he : Extends B (VacuumMassProtection.mass bare (family J) f v hv p))
    (hz : offset f B bare = 0) :
    Preserves B (VacuumMassProtection.mass bare (family J) f v hv p) ↔
      p ∈ (obstruction J f v B).ker := by
  rw [protected_iff J f v B bare hv p he, hz, neg_zero]
  rfl

theorem fiber_iff (p p0 : P)
    (h0 : obstruction J f v B p0 = -offset f B bare) :
    obstruction J f v B p = -offset f B bare ↔
      p - p0 ∈ (obstruction J f v B).ker := by
  change _ ↔ obstruction J f v B (p - p0) = 0
  rw [map_sub, h0, sub_eq_zero]

theorem exists_iff_range :
    (∃ p, obstruction J f v B p = -offset f B bare) ↔
      -offset f B bare ∈ (obstruction J f v B).range := by
  rfl

theorem protected_fiber_iff (p p0 : P)
    (he : ∀ q, Extends B (VacuumMassProtection.mass bare (family J) f v hv q))
    (h0 : Preserves B (VacuumMassProtection.mass bare (family J) f v hv p0)) :
    Preserves B (VacuumMassProtection.mass bare (family J) f v hv p) ↔
      p - p0 ∈ (obstruction J f v B).ker := by
  rw [protected_iff J f v B bare hv p (he p)]
  exact fiber_iff J f v B bare p p0
    ((protected_iff J f v B bare hv p0 (he p0)).mp h0)

theorem universal_iff :
    (∀ p, obstruction J f v B p = -offset f B bare) ↔
      obstruction J f v B = 0 ∧ offset f B bare = 0 := by
  constructor
  · intro h
    have hz : offset f B bare = 0 := by
      have hh := h 0
      rw [map_zero] at hh
      exact neg_eq_zero.mp hh.symm
    refine ⟨?_, hz⟩
    ext p x w
    have hh := h p
    rw [hz, neg_zero] at hh
    exact LinearMap.congr_fun (congrArg (fun C => C x) hh) w
  · rintro ⟨hj, hz⟩ p
    rw [hj, hz]
    simp

theorem family_protected_iff
    (he : ∀ p, Extends B (VacuumMassProtection.mass bare (family J) f v hv p)) :
    (∀ p, Preserves B (VacuumMassProtection.mass bare (family J) f v hv p)) ↔
      obstruction J f v B = 0 ∧ offset f B bare = 0 := by
  rw [← universal_iff J f v B bare]
  constructor
  · intro h p
    exact (protected_iff J f v B bare hv p (he p)).mp (h p)
  · intro h p
    exact (protected_iff J f v B bare hv p (he p)).mpr (h p)

omit B in
theorem generated_exact_iff (L : Submodule ℂ (V × W)) (p : P) :
    (VacuumMassProtection.mass bare (family J) f v hv p).radical.toSubmodule = L ↔
      ∃ h : L ≤ (VacuumMassProtection.mass bare (family J) f v hv p).radical.toSubmodule,
        (ExactRadical.quotientForm
          (VacuumMassProtection.mass bare (family J) f v hv p) L h).Nondegenerate :=
  ExactRadical.exact_iff _ L

end
end Physics.YukawaProtectionKernel
