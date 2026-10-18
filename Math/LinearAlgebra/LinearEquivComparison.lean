import Mathlib.LinearAlgebra.Pi

/-! Small comparison diagrams avoid expanding large constructed quotient equivalences. -/
namespace Math.LinearEquivComparison
set_option autoImplicit false
variable {k A B C : Type*} [Field k]
  [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
  [AddCommMonoid C] [Module k C]

def comparison (e : A ≃ₗ[k] B) (f : A ≃ₗ[k] C) : B ≃ₗ[k] C := e.symm.trans f

theorem extraction (e : A ≃ₗ[k] B) (f : A ≃ₗ[k] C) (x : A) :
    comparison e f (e x) = f x := by
  unfold comparison
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem reconstruction (e : A ≃ₗ[k] B) (f : A ≃ₗ[k] C) (y : B) :
    e.symm y = f.symm (comparison e f y) := (f.symm_apply_apply (e.symm y)).symm

theorem inverse_left (e : A ≃ₗ[k] B) (x : A) : e.symm (e x) = x := e.symm_apply_apply x

theorem inverse_right (e : A ≃ₗ[k] B) (y : B) : e (e.symm y) = y := e.apply_symm_apply y

theorem forbidden (e : A ≃ₗ[k] B) : (∀ x : A, x = 0) ↔ ∀ y : B, y = 0 := by
  constructor
  · intro h y
    calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = e 0 := congrArg e (h (e.symm y))
      _ = 0 := e.map_zero
  · intro h x; exact e.map_eq_zero_iff.mp (h _)

theorem nonzero (e : A ≃ₗ[k] B) : (∃ x : A, x ≠ 0) ↔ ∃ y : B, y ≠ 0 := by
  constructor
  · rintro ⟨x,hx⟩; exact ⟨e x, fun h => hx (e.map_eq_zero_iff.mp h)⟩
  · rintro ⟨y,hy⟩; exact ⟨e.symm y, fun h => hy (e.symm.map_eq_zero_iff.mp h)⟩

end Math.LinearEquivComparison
