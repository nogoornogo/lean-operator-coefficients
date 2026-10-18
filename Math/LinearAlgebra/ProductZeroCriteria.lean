import Mathlib.LinearAlgebra.Pi

/-! Zero and nonzero criteria for an explicit product classification. -/
namespace Math.ProductZeroCriteria
set_option autoImplicit false
noncomputable section
variable {k A I : Type*} [Field k] [AddCommGroup A] [Module k A]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (e : A ≃ₗ[k] (∀ i, V i))

include e in
theorem forbidden_iff : (∀ a : A, a = 0) ↔ ∀ i, ∀ v : V i, v = 0 := by
  classical
  constructor
  · intro h i v
    have he := congrArg e (h (e.symm (Pi.single i v)))
    rw [e.apply_symm_apply, e.map_zero] at he
    simpa using congrFun he i
  · intro h a
    apply e.injective
    rw [e.map_zero]
    exact funext (fun i => h i (e a i))

include e in
theorem nonzero_iff : (∃ a : A, a ≠ 0) ↔ ∃ i, ∃ v : V i, v ≠ 0 := by
  simpa only [not_forall, not_not] using not_congr (forbidden_iff e)

end
end Math.ProductZeroCriteria
