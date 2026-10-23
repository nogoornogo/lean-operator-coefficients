import Math.RepresentationTheory.Exterior.SixSlotAlternation

/-! A certified enumeration of the 2! 4! species permutations and the
restriction of full alternatization to those permutations. -/
-- Check finite certificates sequentially to avoid blocked elaboration worker stacks.
set_option Elab.async false

namespace Math.SixSlotSpeciesSum
set_option autoImplicit false
noncomputable section
open SixSlotAlternation
open scoped TensorProduct

def downIndex : Fin 24 → Fin 4 → Fin 4 := ![
  ![0,1,2,3], ![0,1,3,2], ![0,2,1,3], ![0,2,3,1], ![0,3,1,2], ![0,3,2,1],
  ![1,0,2,3], ![1,0,3,2], ![1,2,0,3], ![1,2,3,0], ![1,3,0,2], ![1,3,2,0],
  ![2,0,1,3], ![2,0,3,1], ![2,1,0,3], ![2,1,3,0], ![2,3,0,1], ![2,3,1,0],
  ![3,0,1,2], ![3,0,2,1], ![3,1,0,2], ![3,1,2,0], ![3,2,0,1], ![3,2,1,0]]

def downParity : Fin 24 → ℤˣ := ![
  1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1,1,-1,-1,1]

private def inverseIndex : Fin 24 → Fin 24 :=
  ![0,1,2,4,3,5,6,7,12,18,13,19,8,10,14,20,16,22,9,11,15,21,17,23]

def slotIndex (r : Fin 2 × Fin 24) : Fin 6 → Fin 6 :=
  ![if r.1 = 0 then 0 else 2,
    ![1,3,4,5] (downIndex r.2 0),
    if r.1 = 0 then 2 else 0,
    ![1,3,4,5] (downIndex r.2 1),
    ![1,3,4,5] (downIndex r.2 2),
    ![1,3,4,5] (downIndex r.2 3)]

private theorem inverse_slot : ∀ r : Fin 2 × Fin 24, ∀ i : Fin 6,
    slotIndex (r.1, inverseIndex r.2) (slotIndex r i) = i := by decide +kernel

private theorem slot_inverse : ∀ r : Fin 2 × Fin 24, ∀ i : Fin 6,
    slotIndex r (slotIndex (r.1, inverseIndex r.2) i) = i := by decide +kernel

def permutation (r : Fin 2 × Fin 24) : Equiv.Perm (Fin 6) where
  toFun := slotIndex r
  invFun := slotIndex (r.1, inverseIndex r.2)
  left_inv := inverse_slot r
  right_inv := slot_inverse r

theorem permutation_preserves : ∀ r, PreservesPattern (permutation r) := by decide +kernel

theorem permutation_injective : Function.Injective permutation := by decide +kernel

theorem permutation_surjective : ∀ p : Equiv.Perm (Fin 6), PreservesPattern p →
    ∃ r, permutation r = p := by decide +kernel

theorem permutation_sign : ∀ r : Fin 2 × Fin 24,
    Equiv.Perm.sign (permutation r) =
      if r.1 = 0 then downParity r.2 else -downParity r.2 := by decide +kernel

theorem sum_preserving (F : Equiv.Perm (Fin 6) → ℂ) :
    (∑ p ∈ Finset.univ.filter PreservesPattern, F p) = ∑ r, F (permutation r) := by
  symm
  apply Finset.sum_bij (fun r _ => permutation r)
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, permutation_preserves r⟩
  · intro r hr s hs he
    exact permutation_injective he
  · intro p hp
    obtain ⟨r, hr⟩ := permutation_surjective p (Finset.mem_filter.mp hp).2
    exact ⟨r, Finset.mem_univ _, hr⟩
  · intro r hr; rfl

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

def blockSum (F : A → B → A → B → B → B → ℂ)
    (u : Fin 2 → A) (d : Fin 4 → B) : ℂ :=
  ∑ r : Fin 24, (downParity r : ℂ) *
    (F (u 0) (d (downIndex r 0)) (u 1) (d (downIndex r 1))
      (d (downIndex r 2)) (d (downIndex r 3)) -
    F (u 1) (d (downIndex r 0)) (u 0) (d (downIndex r 1))
      (d (downIndex r 2)) (d (downIndex r 3)))

theorem alternating_slots_sum (f : OrderedSpace A B →ₗ[ℂ] ℂ)
    (u₁ u₂ : A) (d₁ d₂ d₃ d₄ : B) :
    alternating f (slots u₁ u₂ d₁ d₂ d₃ d₄) =
      ∑ r : Fin 2 × Fin 24, Equiv.Perm.sign (permutation r) •
        ordered f (slots u₁ u₂ d₁ d₂ d₃ d₄ ∘ permutation r) := by
  classical
  unfold alternating
  rw [MultilinearMap.alternatization_apply]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter PreservesPattern))]
  · exact sum_preserving _
  · intro p hp hn
    have hbad : ¬ PreservesPattern p := by simpa using hn
    by_cases h0 : p 0 = 0 ∨ p 0 = 2
    · have h2 : ¬ (p 2 = 0 ∨ p 2 = 2) := fun h => hbad ⟨h0, h⟩
      generalize hk : p 2 = k
      fin_cases k <;> simp_all [ordered, slots, PreservesPattern]
    · generalize hk : p 0 = k
      fin_cases k <;> simp_all [ordered, slots, PreservesPattern]

theorem alternating_slots_block (f : OrderedSpace A B →ₗ[ℂ] ℂ)
    (u : Fin 2 → A) (d : Fin 4 → B) :
    alternating f (slots (u 0) (u 1) (d 0) (d 1) (d 2) (d 3)) =
      blockSum (fun a b c e x y => f (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ]
        (c ⊗ₜ[ℂ] e)) ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y))) u d := by
  rw [alternating_slots_sum, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [permutation_sign, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false]
  simp only [ordered, MultilinearMap.mk'_apply, Function.comp_apply,
    permutation, slotIndex, Equiv.coe_fn_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    slots]
  fin_cases r <;>
    simp [downIndex, downParity, Units.smul_def,
      ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, sub_eq_add_neg, mul_add]

end
end Math.SixSlotSpeciesSum
