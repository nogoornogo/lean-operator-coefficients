import Math.RepresentationTheory.Exterior.FourSlotTripleAlternation

/-! The explicit six-term unnormalized exterior orbit of three equal slots. -/
namespace Math.FourSlotTripleAlternation
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

private def p01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1
private def p12 : Equiv.Perm (Fin 4) := Equiv.swap 1 2
private def six : Fin 6 → Equiv.Perm (Fin 4) :=
  ![1, p01, p12, p01*p12, p12*p01, p01*p12*p01]

theorem alternating_slots_orbit (f : Tensor (A := A) (B := B) →ₗ[ℂ] ℂ)
    (x y z : A) (h : B) : alternating f (slots x y z h) =
    f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) -
    f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) -
    f ((x ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] h)) +
    f ((y ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] h)) +
    f ((z ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] h)) -
    f ((z ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] h)) := by
  classical
  have hp : Finset.univ.filter (fun p : Equiv.Perm (Fin 4) => p 3 = 3) =
      Finset.univ.image six := by decide +kernel
  have hi : Function.Injective six := by decide +kernel
  have hn (i : Fin 4) (hi : i ≠ 3) : (slots x y z h i).2 = 0 := by
    fin_cases i <;> simp_all [slots]
  rw [alternating, MultilinearMap.alternatization_apply]
  trans ∑ p : Equiv.Perm (Fin 4), if p 3 = 3 then
    Equiv.Perm.sign p • ordered f (slots x y z h ∘ p) else 0
  · apply Finset.sum_congr rfl
    intro p _
    by_cases hlast : p 3 = 3
    · simp only [hlast, ↓reduceIte, MultilinearMap.domDomCongr_apply]
      rfl
    · simp [hlast, MultilinearMap.domDomCongr_apply, ordered, hn _ hlast]
  · rw [← Finset.sum_filter, hp]
    rw [Finset.sum_image (by intro p _ q _ hpq; exact hi hpq)]
    norm_num [Fin.sum_univ_succ, six, p01, p12, ordered, slots,
      Equiv.swap_apply_def, Fin.ext_iff, Equiv.Perm.sign_mul]
    ring

end
end Math.FourSlotTripleAlternation
