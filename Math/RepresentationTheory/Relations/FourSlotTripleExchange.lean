import Math.RepresentationTheory.Exterior.FourSlotTripleAlternation

/-! Two adjacent exchanges suffice for alternation of three identical slots. -/
namespace Math.FourSlotTripleAlternation
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

private def s01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1
private def s12 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

private theorem fixing_last (p : Equiv.Perm (Fin 4)) (hp : p 3 = 3) :
    p = 1 ∨ p = s01 ∨ p = s12 ∨ p = s01 * s12 ∨ p = s12 * s01 ∨
      p = s01 * s12 * s01 := by
  have h : ∀ p : Equiv.Perm (Fin 4), p 3 = 3 →
      p = 1 ∨ p = s01 ∨ p = s12 ∨ p = s01 * s12 ∨ p = s12 * s01 ∨
        p = s01 * s12 * s01 := by decide +kernel
  exact h p hp

theorem alternates_iff_adjacent (f : Tensor (A := A) (B := B) →ₗ[ℂ] ℂ) :
    Alternates f ↔
      (∀ x y z h, f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) =
        -f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))) ∧
      (∀ x y z h, f ((x ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] h)) =
        -f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))) := by
  constructor
  · intro hf
    constructor
    · intro x y z h
      have he := hf s01 (by decide) x y z h
      simpa [ordered, slots, s01, Equiv.swap_apply_def, Fin.ext_iff] using he
    · intro x y z h
      have he := hf s12 (by decide) x y z h
      simpa [ordered, slots, s12, Equiv.swap_apply_def, Fin.ext_iff] using he
  · rintro ⟨h01, h12⟩ p hp x y z h
    rcases fixing_last p hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [ordered, slots, s01, s12,
      Equiv.swap_apply_def, Fin.ext_iff]
    all_goals grind only

def swap01 : Tensor (A := A) (B := B) ≃ₗ[ℂ] Tensor (A := A) (B := B) :=
  TensorProduct.congr (TensorProduct.comm ℂ A A) (LinearEquiv.refl ℂ _)

def swap12 : Tensor (A := A) (B := B) ≃ₗ[ℂ] Tensor (A := A) (B := B) :=
  TensorProduct.tensorTensorTensorComm ℂ A A A B

theorem alternates_iff_comp (f : Tensor (A := A) (B := B) →ₗ[ℂ] ℂ) :
    Alternates f ↔ f.comp swap01.toLinearMap = -f ∧
      f.comp swap12.toLinearMap = -f := by
  rw [alternates_iff_adjacent]
  constructor
  · rintro ⟨h01, h12⟩
    constructor
    all_goals
      apply TensorProduct.ext
      apply TensorProduct.ext
      apply LinearMap.ext; intro x
      apply LinearMap.ext; intro y
      apply TensorProduct.ext
      apply LinearMap.ext; intro z
      apply LinearMap.ext; intro h
    · exact h01 x y z h
    · exact h12 x y z h
  · rintro ⟨h01, h12⟩
    constructor
    · intro x y z h
      exact DFunLike.congr_fun h01 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))
    · intro x y z h
      exact DFunLike.congr_fun h12 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h))

end
end Math.FourSlotTripleAlternation
