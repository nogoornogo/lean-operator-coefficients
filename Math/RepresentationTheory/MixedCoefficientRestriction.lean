import Math.RepresentationTheory.MixedSpeciesProjection
import Math.RepresentationTheory.InvariantHomRestriction

/-! Residual-group restriction on independently supported mixed coefficients. -/
namespace Math.MixedCoefficientRestriction
set_option autoImplicit false
noncomputable section
open Representation
variable {H J P Q : Type*} [Group H] [Group J]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {V : P → Type*} {W : Q → Type*}
  [∀ u, AddCommGroup (V u)] [∀ u, Module ℂ (V u)]
  [∀ u, AddCommGroup (W u)] [∀ u, Module ℂ (W u)]
  (r : ∀ u, Representation ℂ H (V u)) (t : ∀ u, Representation ℂ H (W u))
  (j : J →* H) (n m : ℕ)

def restrict : MixedWeightSupport.Coefficient (FiniteSpeciesExterior.representation r)
    (FiniteSpeciesExterior.representation t) (n := n) (m := m) →ₗ[ℂ]
    MixedWeightSupport.Coefficient (FiniteSpeciesExterior.representation (fun u => (r u).comp j))
      (FiniteSpeciesExterior.representation (fun u => (t u).comp j)) (n := n) (m := m) where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' h := f.isIntertwining' (j h) }
  map_add' _ _ := IntertwiningMap.ext rfl
  map_smul' _ _ := IntertwiningMap.ext rfl

theorem injective : Function.Injective (restrict r t j n m) := by
  intro f g h
  apply IntertwiningMap.ext
  exact congrArg (fun f => f.toLinearMap) h

variable (allow : (Fin n → P) → (Fin m → Q) → Prop)

def selected : MixedSpeciesProjection.supportSpace allow r t →ₗ[ℂ]
    MixedSpeciesProjection.supportSpace allow (fun u => (r u).comp j) (fun u => (t u).comp j) where
  toFun f := ⟨restrict r t j n m f.val, f.property⟩
  map_add' _ _ := by apply Subtype.ext; ext u; rfl
  map_smul' _ _ := by apply Subtype.ext; ext u; rfl

theorem selected_injective : Function.Injective (selected r t j n m allow) := by
  intro f g h
  apply Subtype.ext
  exact (injective r t j n m) (congrArg Subtype.val h)

theorem nonzero (h : ∃ f : MixedSpeciesProjection.supportSpace allow r t, f ≠ 0) :
    ∃ f : MixedSpeciesProjection.supportSpace allow
      (fun u => (r u).comp j) (fun u => (t u).comp j), f ≠ 0 := by
  obtain ⟨f,hf⟩ := h
  exact ⟨selected r t j n m allow f, fun hz => hf ((selected_injective r t j n m allow)
    (hz.trans (selected r t j n m allow).map_zero.symm))⟩

theorem forbidden (h : ∀ f : MixedSpeciesProjection.supportSpace allow
    (fun u => (r u).comp j) (fun u => (t u).comp j), f = 0) :
    ∀ f : MixedSpeciesProjection.supportSpace allow r t, f = 0 := by
  intro f
  exact (selected_injective r t j n m allow)
    ((h _).trans (selected r t j n m allow).map_zero.symm)

def surjectiveEquiv (hj : Function.Surjective j) :
    MixedSpeciesProjection.supportSpace allow r t ≃ₗ[ℂ]
    MixedSpeciesProjection.supportSpace allow (fun u => (r u).comp j) (fun u => (t u).comp j) where
  toFun := selected r t j n m allow
  invFun f := ⟨{
    toLinearMap := f.val.toLinearMap
    isIntertwining' h := by obtain ⟨g,rfl⟩ := hj h; exact f.val.isIntertwining' g }, f.property⟩
  left_inv _ := by apply Subtype.ext; exact IntertwiningMap.ext rfl
  right_inv _ := by apply Subtype.ext; exact IntertwiningMap.ext rfl
  map_add' := (selected r t j n m allow).map_add
  map_smul' := (selected r t j n m allow).map_smul

theorem selected_id (f : MixedSpeciesProjection.supportSpace allow r t) :
    selected r t (MonoidHom.id H) n m allow f = f := by
  apply Subtype.ext
  exact IntertwiningMap.ext rfl

theorem selected_comp {J' : Type*} [Group J'] (i : J' →* J)
    (f : MixedSpeciesProjection.supportSpace allow r t) :
    selected (fun u => (r u).comp j) (fun u => (t u).comp j) i n m allow
      (selected r t j n m allow f) = selected r t (j.comp i) n m allow f := by
  apply Subtype.ext
  exact IntertwiningMap.ext rfl

section AllDegrees
variable (allowed : ∀ n m : ℕ, (Fin n → P) → (Fin m → Q) → Prop)

def allMap : (∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2) r t) →ₗ[ℂ]
    (∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2)
      (fun u => (r u).comp j) (fun u => (t u).comp j)) :=
  LinearMap.pi fun z => (selected r t j z.1 z.2 (allowed z.1 z.2)).comp (LinearMap.proj z)

theorem all_injective : Function.Injective (allMap r t j allowed) := by
  intro f g h
  funext z
  exact (selected_injective r t j z.1 z.2 (allowed z.1 z.2)) (congrFun h z)

theorem all_forbidden
    (h : ∀ n m, ∀ f : MixedSpeciesProjection.supportSpace (allowed n m)
      (fun u => (r u).comp j) (fun u => (t u).comp j), f = 0) :
    ∀ n m, ∀ f : MixedSpeciesProjection.supportSpace (allowed n m) r t, f = 0 := by
  intro n m
  exact forbidden r t j n m (allowed n m) (h n m)

theorem all_nonzero
    (h : ∃ n m, ∃ f : MixedSpeciesProjection.supportSpace (allowed n m) r t, f ≠ 0) :
    ∃ n m, ∃ f : MixedSpeciesProjection.supportSpace (allowed n m)
      (fun u => (r u).comp j) (fun u => (t u).comp j), f ≠ 0 := by
  obtain ⟨n,m,h⟩ := h
  exact ⟨n,m,nonzero r t j n m (allowed n m) h⟩

def allSurjectiveEquiv (hj : Function.Surjective j) :
    (∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2) r t) ≃ₗ[ℂ]
    (∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2)
      (fun u => (r u).comp j) (fun u => (t u).comp j)) :=
  LinearEquiv.piCongrRight fun z => surjectiveEquiv r t j z.1 z.2 (allowed z.1 z.2) hj
end AllDegrees
end
end Math.MixedCoefficientRestriction
