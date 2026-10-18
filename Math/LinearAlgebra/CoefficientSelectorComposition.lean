import Mathlib.LinearAlgebra.Pi

/-! Independent coefficient selectors, without an assumed physical flavor basis. -/
namespace Math.CoefficientSelectorComposition
set_option autoImplicit false
variable {k V X I : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup X] [Module k X] {W : I → Type*}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
def combine (s : ∀ i, V →ₗ[k] W i) : V →ₗ[k] (∀ i, W i) := LinearMap.pi s

theorem combine_zero_iff (s : ∀ i, V →ₗ[k] W i) : combine s = 0 ↔ ∀ i, s i = 0 := by
  constructor
  · intro h i; ext v
    exact congrFun (LinearMap.congr_fun h v) i
  · intro h; ext v i; exact LinearMap.congr_fun (h i) v

theorem transport_zero_iff {Y : Type*} [AddCommGroup Y] [Module k Y]
    (e : V ≃ₗ[k] X) (s : X →ₗ[k] Y) : s.comp e.toLinearMap = 0 ↔ s = 0 := by
  constructor
  · intro h; ext x; obtain ⟨v,rfl⟩ := e.surjective x
    exact LinearMap.congr_fun h v
  · rintro rfl; rfl

theorem restriction_square {Y : Type*} [AddCommGroup Y] [Module k Y]
    (r : V →ₗ[k] X) (s : V →ₗ[k] Y) (t : X →ₗ[k] Y)
    (h : ∀ v, s v = t (r v)) : s = t.comp r := LinearMap.ext h

/-- Empty intersection is compatible with nonempty constituents. -/
theorem intersection_not_union :
    (∀ x : Bool, (x = true ∧ x = false) → False) ∧
    ¬ (∀ x : Bool, (x = true ∨ x = false) → False) := by
  constructor
  · rintro x ⟨rfl,h⟩; cases h
  · intro h; exact h true (Or.inl rfl)
end Math.CoefficientSelectorComposition
