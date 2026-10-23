import Mathlib.LinearAlgebra.Quotient.Basic

/-! Coordinate completeness restricted to independently specified linear
constraints. No representation, dimension or statistics premise is imposed. -/
namespace Math.ConstrainedCompleteness
set_option autoImplicit false
noncomputable section

variable {k A B C : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

/-- A coordinate classification plus a proved equivalence of constraints.
The submodules are independent inputs, not defined as the image of `coordinates`. -/
structure Presentation (S : Submodule k A) (T : Submodule k B) where
  coordinates : A ≃ₗ[k] B
  admissible : ∀ x, x ∈ S ↔ coordinates x ∈ T

namespace Presentation
variable {S : Submodule k A} {T : Submodule k B}

def equiv (p : Presentation S T) : S ≃ₗ[k] T where
  toFun x := ⟨p.coordinates x, (p.admissible x).mp x.property⟩
  invFun y := ⟨p.coordinates.symm y, (p.admissible _).mpr (by simp [y.property])⟩
  left_inv x := by apply Subtype.ext; exact p.coordinates.symm_apply_apply x
  right_inv y := by apply Subtype.ext; exact p.coordinates.apply_symm_apply y
  map_add' x y := by apply Subtype.ext; exact p.coordinates.map_add x y
  map_smul' z x := by apply Subtype.ext; exact p.coordinates.map_smul z x

@[simp] theorem equiv_apply (p : Presentation S T) (x : S) :
    (p.equiv x : B) = p.coordinates x := rfl

@[simp] theorem equiv_symm_apply (p : Presentation S T) (y : T) :
    (p.equiv.symm y : A) = p.coordinates.symm y := rfl

/-- Transport an independent actual sector before coordinate extraction. -/
def onInputs {U : Submodule k C} (p : Presentation S T)
    (input : Presentation U S) : U ≃ₗ[k] T := input.equiv.trans p.equiv

@[simp] theorem onInputs_apply {U : Submodule k C} (p : Presentation S T)
    (input : Presentation U S) (x : U) :
    (p.onInputs input x : B) = p.coordinates (input.coordinates x) := rfl

end Presentation

/-- A commuting system of linear equations supplies the constraint certificate.
Neither kernel is defined by transport through the coordinate map. -/
def ofEquations {E : Type*} [AddCommGroup E] [Module k E]
    (coordinates : A ≃ₗ[k] B) (source : A →ₗ[k] E) (target : B →ₗ[k] E)
    (commutes : ∀ x, target (coordinates x) = source x) :
    Presentation (LinearMap.ker source) (LinearMap.ker target) where
  coordinates := coordinates
  admissible x := by simp only [LinearMap.mem_ker, commutes]

/-- Completeness transports existence, not a physical generation assumption. -/
theorem exists_nonzero_iff (e : A ≃ₗ[k] B) :
    (∃ x : A, x ≠ 0) ↔ ∃ y : B, y ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨e x, fun h => hx (e.map_eq_zero_iff.mp h)⟩
  · rintro ⟨y, hy⟩
    exact ⟨e.symm y, fun h => hy (e.symm.map_eq_zero_iff.mp h)⟩

end
end Math.ConstrainedCompleteness
