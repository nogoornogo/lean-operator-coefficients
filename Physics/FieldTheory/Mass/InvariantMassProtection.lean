import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.RepresentationTheory.Decomposition.CommonIrreducible

open Math

/-! Classification of invariant mass extensions preserving a fixed radical.
The general criterion concerns restrictions of ambient intertwiners; a
retraction is needed to replace it by all intertwiners on the radical. -/
set_option autoImplicit false
namespace GUT.InvariantMassProtection
noncomputable section
open Representation InvariantWeylMass

variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {rho : Representation ℂ G V} {sigma : Representation ℂ G W}

def lightInclusion (B : SymmetricMass rho) : IntertwiningMap B.radical.toRepresentation rho where
  toLinearMap := B.radical.toSubmodule.subtype
  isIntertwining' _ := rfl

def cross (F : SymmetricMass (rho.prod sigma)) : IntertwiningMap rho sigma.dual where
  toLinearMap := (F.form.compl₁₂ (LinearMap.inl ℂ V W) (LinearMap.inr ℂ V W))
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro w
    change F.form (rho g x, 0) (0, w) = F.form (x, 0) (0, sigma g⁻¹ w)
    have h := F.form_covariant g (x, 0) (0, w)
    change F.form (rho g x, sigma g 0) (0, w) =
      F.form (x, 0) (rho g⁻¹ 0, sigma g⁻¹ w) at h
    simpa only [map_zero] using h

def block (B : SymmetricMass rho) (D : SymmetricMass sigma)
    (C : IntertwiningMap rho sigma.dual) : SymmetricMass (rho.prod sigma) where
  form := B.form.compl₁₂ (LinearMap.fst ℂ V W) (LinearMap.fst ℂ V W) +
    C.toLinearMap.compl₁₂ (LinearMap.fst ℂ V W) (LinearMap.snd ℂ V W) +
    C.toLinearMap.flip.compl₁₂ (LinearMap.snd ℂ V W) (LinearMap.fst ℂ V W) +
    D.form.compl₁₂ (LinearMap.snd ℂ V W) (LinearMap.snd ℂ V W)
  symmetric := by
    constructor
    intro x y
    change B.form x.1 y.1 + C x.1 y.2 + C y.1 x.2 + D.form x.2 y.2 =
      B.form y.1 x.1 + C y.1 x.2 + C x.1 y.2 + D.form y.2 x.2
    rw [B.symmetric.eq x.1 y.1, D.symmetric.eq x.2 y.2]
    ring
  invariant g x y := by
    have hc (v : V) (w : W) : C (rho g v) (sigma g w) = C v w := by
      rw [C.isIntertwining rho sigma.dual g v]
      change C v (sigma g⁻¹ (sigma g w)) = C v w
      simp
    change B.form (rho g x.1) (rho g y.1) + C (rho g x.1) (sigma g y.2) +
      C (rho g y.1) (sigma g x.2) + D.form (sigma g x.2) (sigma g y.2) = _
    rw [B.invariant, D.invariant, hc, hc]
    rfl

@[simp] theorem block_apply (B : SymmetricMass rho) (D : SymmetricMass sigma)
    (C : IntertwiningMap rho sigma.dual) (x y : V × W) :
    (block B D C).form x y =
      B.form x.1 y.1 + C x.1 y.2 + C y.1 x.2 + D.form x.2 y.2 := rfl

def Extends (B : SymmetricMass rho) (F : SymmetricMass (rho.prod sigma)) : Prop :=
  ∀ x y, F.form (x, 0) (y, 0) = B.form x y

def Preserves (B : SymmetricMass rho) (F : SymmetricMass (rho.prod sigma)) : Prop :=
  ∀ x : B.radical.toSubmodule, (x.val, 0) ∈ F.radical.toSubmodule

def radicalMap (B : SymmetricMass rho) (F : SymmetricMass (rho.prod sigma))
    (h : Preserves B F) : IntertwiningMap B.radical.toRepresentation
      F.radical.toRepresentation where
  toLinearMap := ((LinearMap.inl ℂ V W).comp B.radical.toSubmodule.subtype).codRestrict
    F.radical.toSubmodule h
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (rho g x.val, 0) = (rho g x.val, sigma g 0)
    rw [map_zero]

theorem radicalMap_injective (B : SymmetricMass rho) (F : SymmetricMass (rho.prod sigma))
    (h : Preserves B F) : Function.Injective (radicalMap B F h) := by
  intro x y he
  exact Subtype.ext (congrArg (fun z => z.val.1) he)

theorem block_extends (B : SymmetricMass rho) (D : SymmetricMass sigma)
    (C : IntertwiningMap rho sigma.dual) : Extends B (block B D C) := by
  intro x y
  simp [block_apply]

theorem cross_block (B : SymmetricMass rho) (D : SymmetricMass sigma)
    (C : IntertwiningMap rho sigma.dual) : cross (block B D C) = C := by
  ext x w
  change (block B D C).form (x, 0) (0, w) = C x w
  simp [block_apply]

theorem preserves_iff (B : SymmetricMass rho) (F : SymmetricMass (rho.prod sigma))
    (hF : Extends B F) :
    Preserves B F ↔ (cross F).comp (lightInclusion B) = 0 := by
  constructor
  · intro h
    ext x w
    exact (F.mem_radical _).mp (h x) (0, w)
  · intro h x
    rw [SymmetricMass.mem_radical]
    rintro ⟨v, w⟩
    have hz : F.form (x.val, 0) (0, w) = 0 :=
      LinearMap.congr_fun (congrArg (fun f => f x) h) w
    have hl : B.form x.val v = 0 := (B.mem_radical _).mp x.property v
    have he : (v, w) = (v, 0) + (0, w) := by simp
    rw [he, map_add, hF, hl, hz, zero_add]

def UniversallyProtected (B : SymmetricMass rho) (sigma : Representation ℂ G W) : Prop :=
  ∀ F : SymmetricMass (rho.prod sigma), Extends B F → Preserves B F

theorem universal_iff_restriction (B : SymmetricMass rho) :
    UniversallyProtected B sigma ↔
      ∀ C : IntertwiningMap rho sigma.dual, C.comp (lightInclusion B) = 0 := by
  constructor
  · intro h C
    have he := (preserves_iff B (block B (SymmetricMass.zero sigma) C)
      (block_extends B _ C)).mp (h _ (block_extends B _ C))
    rwa [cross_block] at he
  · intro h F hF
    exact (preserves_iff B F hF).mpr (h (cross F))

theorem universal_of_hom_zero (B : SymmetricMass rho)
    (h : ∀ f : IntertwiningMap B.radical.toRepresentation sigma.dual, f = 0) :
    UniversallyProtected B sigma :=
  (universal_iff_restriction B).mpr (fun C => h (C.comp (lightInclusion B)))

theorem universal_iff_hom_zero_of_retraction (B : SymmetricMass rho)
    (p : IntertwiningMap rho B.radical.toRepresentation)
    (hp : ∀ x, p (lightInclusion B x) = x) :
    UniversallyProtected B sigma ↔
      ∀ f : IntertwiningMap B.radical.toRepresentation sigma.dual, f = 0 := by
  constructor
  · intro h f
    have hz := (universal_iff_restriction B).mp h (f.comp p)
    ext x w
    have he := LinearMap.congr_fun (congrArg (fun k => k x) hz) w
    change f (p (lightInclusion B x)) w = 0 at he
    rwa [hp] at he
  · exact universal_of_hom_zero B

theorem universal_iff_hom_zero (B : SymmetricMass rho)
    (hr : IsSemisimpleRepresentation rho) :
    UniversallyProtected B sigma ↔
      ∀ f : IntertwiningMap B.radical.toRepresentation sigma.dual, f = 0 := by
  obtain ⟨S, hS⟩ := SemisimpleSplitting.exists_retraction rho B.radical.toRepresentation
    hr (lightInclusion B) Subtype.val_injective
  apply universal_iff_hom_zero_of_retraction B S.project
  intro x
  rw [← hS]
  exact S.left_inv x

theorem light_semisimple (B : SymmetricMass rho)
    (hr : IsSemisimpleRepresentation rho) :
    IsSemisimpleRepresentation B.radical.toRepresentation := by
  let := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule rho).mp hr
  apply (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
  exact IsSemisimpleModule.of_injective
    (IntertwiningMap.equivLinearMapAsModule _ _ (lightInclusion B)) Subtype.val_injective

theorem universal_iff_no_common (B : SymmetricMass rho)
    (hr : IsSemisimpleRepresentation rho) :
    UniversallyProtected B sigma ↔
      ¬ CommonIrreducible.Shares B.radical.toRepresentation sigma.dual :=
  (universal_iff_hom_zero B hr).trans
    (CommonIrreducible.all_zero_iff _ _ (light_semisimple B hr))

theorem family_iff {P : Type*} (B : SymmetricMass rho)
    (F : P → SymmetricMass (rho.prod sigma)) (hF : ∀ p, Extends B (F p)) :
    (∀ p, Preserves B (F p)) ↔
      ∀ p, (cross (F p)).comp (lightInclusion B) = 0 := by
  constructor
  · intro h p
    exact (preserves_iff B (F p) (hF p)).mp (h p)
  · intro h p
    exact (preserves_iff B (F p) (hF p)).mpr (h p)

theorem exists_lifting_iff_common (B : SymmetricMass rho)
    (hr : IsSemisimpleRepresentation rho) :
    (∃ F : SymmetricMass (rho.prod sigma), Extends B F ∧ ¬ Preserves B F) ↔
      CommonIrreducible.Shares B.radical.toRepresentation sigma.dual := by
  classical
  have h := not_congr (universal_iff_no_common (sigma := sigma) B hr)
  simpa only [UniversallyProtected, not_forall, not_imp, not_not, exists_prop] using h

end
end GUT.InvariantMassProtection
