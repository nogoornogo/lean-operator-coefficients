import Math.RepresentationTheory.Decomposition.SurjectiveHomTransport
import Math.RepresentationTheory.FamilyStabilizer

/-! Restriction preserves nonzero invariant functionals; surjectivity gives equality. -/
namespace Math.InvariantHomRestriction
set_option autoImplicit false
noncomputable section
open Representation
variable {k H K V : Type*} [Field k] [Group H] [Group K]
  [AddCommGroup V] [Module k V]
  (a : Representation k H V) (j : K →* H)

abbrev Space := IntertwiningMap a (trivial k H k)

def restrict : Space a →ₗ[k] Space (a.comp j) where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' g := f.isIntertwining' (j g) }
  map_add' _ _ := IntertwiningMap.ext rfl
  map_smul' _ _ := IntertwiningMap.ext rfl

@[simp] theorem restrict_apply (f : Space a) (v : V) : restrict a j f v = f v := rfl

theorem injective : Function.Injective (restrict a j) := by
  intro f g h
  apply IntertwiningMap.ext
  exact congrArg (fun f => f.toLinearMap) h

theorem nonzero (h : ∃ f : Space a, f ≠ 0) : ∃ f : Space (a.comp j), f ≠ 0 := by
  obtain ⟨f,hf⟩ := h
  exact ⟨restrict a j f, fun hz => hf ((injective a j) (hz.trans (restrict a j).map_zero.symm))⟩

theorem forbidden (h : ∀ f : Space (a.comp j), f = 0) : ∀ f : Space a, f = 0 := by
  intro f
  exact (injective a j) ((h _).trans (restrict a j).map_zero.symm)

def surjectiveEquiv (hj : Function.Surjective j) : Space a ≃ₗ[k] Space (a.comp j) where
  toFun := restrict a j
  invFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' h := by obtain ⟨g,rfl⟩ := hj h; exact f.isIntertwining' g }
  left_inv _ := IntertwiningMap.ext rfl
  right_inv _ := IntertwiningMap.ext rfl
  map_add' := (restrict a j).map_add
  map_smul' := (restrict a j).map_smul

theorem restrict_id (f : Space a) : restrict a (MonoidHom.id H) f = f :=
  IntertwiningMap.ext rfl

theorem restrict_comp {J : Type*} [Group J] (i : J →* K) (f : Space a) :
    restrict (a.comp j) i (restrict a j f) = restrict a (j.comp i) f :=
  IntertwiningMap.ext rfl

theorem subgroup_nonzero (S T : Subgroup H) (hST : S ≤ T)
    (h : ∃ f : Space (a.comp T.subtype), f ≠ 0) :
    ∃ f : Space (a.comp S.subtype), f ≠ 0 :=
  nonzero (a.comp T.subtype) (Subgroup.inclusion hST) h

theorem subgroup_forbidden (S T : Subgroup H) (hST : S ≤ T)
    (h : ∀ f : Space (a.comp S.subtype), f = 0) :
    ∀ f : Space (a.comp T.subtype), f = 0 :=
  forbidden (a.comp T.subtype) (Subgroup.inclusion hST) h
end
end Math.InvariantHomRestriction
