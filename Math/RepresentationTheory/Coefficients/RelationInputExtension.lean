import Math.RepresentationTheory.Relations.RelationQuotient

/-! Add constraints to a proved coefficient presentation without changing its API.
The added input relations are images of actual source relations. -/
namespace Math.RelationInputExtension
set_option autoImplicit false
noncomputable section
open Representation
variable {k H U V W C : Type*} [Field k] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup C] [Module k C]
  (rho : Representation k H V) (tau : Representation k H W)
  (e : C ≃ₗ[k] IntertwiningMap rho tau) (q : U →ₗ[k] V)
  (value : C →ₗ[k] (U →ₗ[k] W))
  (evaluation : ∀ c u, e c (q u) = value c u) (T : Submodule k U)

def Input : Submodule k C where
  carrier := {c | T ≤ (value c).ker}
  zero_mem' := by intro u hu; simp
  add_mem' := by
    intro c d hc hd u hu
    change value (c + d) u = 0
    rw [map_add, LinearMap.add_apply, hc hu, hd hu, add_zero]
  smul_mem' := by
    intro z c hc u hu
    change value (z • c) u = 0
    rw [map_smul, LinearMap.smul_apply, hc hu, smul_zero]

abbrev relations : Submodule k V := T.map q

include evaluation in
theorem admissible_iff (c : C) : c ∈ Input value T ↔
    e c ∈ RelationQuotient.vanishing rho tau (relations q T) := by
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    exact (evaluation c u).trans (h hu)
  · intro h u hu
    exact (evaluation c u).symm.trans (h ⟨u, hu, rfl⟩)

def constrainedEquiv : Input value T ≃ₗ[k]
    RelationQuotient.vanishing rho tau (relations q T) where
  toFun c := ⟨e c.val, (admissible_iff rho tau e q value evaluation T c.val).mp c.property⟩
  invFun f := ⟨e.symm f.val, (admissible_iff rho tau e q value evaluation T _).mpr (by
    simpa only [e.apply_symm_apply] using f.property)⟩
  left_inv c := Subtype.ext (e.symm_apply_apply c.val)
  right_inv f := Subtype.ext (e.apply_symm_apply f.val)
  map_add' c d := Subtype.ext (e.map_add c.val d.val)
  map_smul' z c := Subtype.ext (e.map_smul z c.val)

def equiv (stable : ∀ h, relations q T ≤ (relations q T).comap (rho h)) :
    Input value T ≃ₗ[k] IntertwiningMap (rho.quotient (relations q T) stable) tau :=
  (constrainedEquiv rho tau e q value evaluation T).trans
    (RelationQuotient.equiv rho tau _ stable)

@[simp] theorem extraction (stable : ∀ h, relations q T ≤ (relations q T).comap (rho h))
    (c : Input value T) (u : U) :
    equiv rho tau e q value evaluation T stable c ((relations q T).mkQ (q u)) = value c.val u :=
  evaluation c.val u

@[simp] theorem reconstruction (stable : ∀ h, relations q T ≤ (relations q T).comap (rho h))
    (f : IntertwiningMap (rho.quotient (relations q T) stable) tau) (u : U) :
    value ((equiv rho tau e q value evaluation T stable).symm f).val u =
      f ((relations q T).mkQ (q u)) := by
  change value (e.symm ((RelationQuotient.equiv rho tau (relations q T) stable).symm f).val) u = _
  rw [← evaluation, e.apply_symm_apply]
  rfl

include e evaluation in
theorem forbidden_iff (stable : ∀ h, relations q T ≤ (relations q T).comap (rho h)) :
    (∀ c : Input value T, c = 0) ↔
    ∀ f : IntertwiningMap (rho.quotient (relations q T) stable) tau, f = 0 := by
  constructor
  · intro h f
    rw [← (equiv rho tau e q value evaluation T stable).apply_symm_apply f, h ((equiv rho tau e q value evaluation T stable).symm f), map_zero]
  · intro h c
    apply (equiv rho tau e q value evaluation T stable).injective
    rw [h ((equiv rho tau e q value evaluation T stable) c), map_zero]

include e evaluation in
theorem nonzero_iff (stable : ∀ h, relations q T ≤ (relations q T).comap (rho h)) :
    (∃ c : Input value T, c ≠ 0) ↔
    ∃ f : IntertwiningMap (rho.quotient (relations q T) stable) tau, f ≠ 0 := by
  simpa only [not_forall, not_not] using
    not_congr (forbidden_iff rho tau e q value evaluation T stable)

variable (source : Representation k H U)

theorem relations_stable
    (hq : ∀ h u, q (source h u) = rho h (q u))
    (hT : ∀ h, T ≤ T.comap (source h)) :
    ∀ h, relations q T ≤ (relations q T).comap (rho h) := by
  rintro h _ ⟨u, hu, rfl⟩
  exact ⟨source h u, hT h hu, hq h u⟩

/-- No added relation: existing coefficient input is recovered without new obligations. -/
def emptyEquiv : Input value (⊥ : Submodule k U) ≃ₗ[k] C where
  toFun c := c.val
  invFun c := ⟨c, show (⊥ : Submodule k U) ≤ (value c).ker from bot_le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem empty_evaluation (c : C) (u : U) :
    value ((emptyEquiv value).symm c).val u = value c u := rfl

end
end Math.RelationInputExtension
