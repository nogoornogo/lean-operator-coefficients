import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.PowersetCard
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Even exterior weights in dimension five, including the determinant-one
identification of degree four with the dual defining weights. -/

set_option autoImplicit false

namespace Math.RankFiveExteriorSum

abbrev EvenIndex := {s : Finset (Fin 5) // s.card % 2 = 0}

theorem by_degree (w : Fin 5 → ℂ) :
    (∑ s : EvenIndex, ∏ i ∈ s.val, w i) =
      1 + (∑ s : Set.powersetCard (Fin 5) 2, ∏ i ∈ s.val, w i) +
        ∑ s : Set.powersetCard (Fin 5) 4, ∏ i ∈ s.val, w i := by
  classical
  have hs (p : Finset (Fin 5) → Prop) [DecidablePred p] [Fintype (Subtype p)] :
      (∑ s : Subtype p, ∏ i ∈ s.val, w i) =
        ∑ s : Finset (Fin 5), if p s then ∏ i ∈ s, w i else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := p) (Finset.univ.filter p) (by intro s; simp)
      (fun s => ∏ i ∈ s, w i)).symm
  have hz : (∑ s : Finset (Fin 5), if s.card = 0 then ∏ i ∈ s, w i else 0) = 1 := by
    simp [Finset.card_eq_zero]
  rw [hs, hs, hs, ← hz, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have hb : s.card ≤ 5 := (Finset.card_le_univ s).trans_eq (Fintype.card_fin 5)
  simp only [Set.powersetCard.mem_iff]
  interval_cases h : s.card <;> simp

theorem degree_four (w : Fin 5 → ℂ) (hp : ∏ i, w i = 1) :
    (∑ s : Set.powersetCard (Fin 5) 4, ∏ i ∈ s.val, w i) = ∑ i, (w i)⁻¹ := by
  classical
  let e : Fin 5 ≃ Set.powersetCard (Fin 5) 4 :=
    Set.powersetCard.ofSingleton.trans (Set.powersetCard.compl (by decide))
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  change (∏ j ∈ ({i} : Finset (Fin 5))ᶜ, w j) = (w i)⁻¹
  have h : w i * (∏ j ∈ ({i} : Finset (Fin 5))ᶜ, w j) = 1 := by
    simpa using (Finset.prod_mul_prod_compl ({i} : Finset (Fin 5)) w).trans hp
  exact eq_inv_of_mul_eq_one_right h

theorem determinant_one (w : Fin 5 → ℂ) (hp : ∏ i, w i = 1) :
    (∑ s : EvenIndex, ∏ i ∈ s.val, w i) =
      1 + (∑ s : Set.powersetCard (Fin 5) 2, ∏ i ∈ s.val, w i) + ∑ i, (w i)⁻¹ := by
  rw [by_degree, degree_four w hp]

end Math.RankFiveExteriorSum
