import Math.LieGroups.E6.Minuscule.CompactTorus
import Math.LieGroups.E6.Minuscule.CubicGroupInvariant

/-! Diagonal candidate elements are reconstructed from six weight coordinates.
The finite elimination equations follow from the actual invariant cubic. -/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Math.E6.Minuscule.Torus

noncomputable section

open scoped Matrix

def coordinateOrder : Fin 27 → Fin 27 :=
  ![2, 3, 4, 9, 21, 23, 18, 25, 14, 16, 7, 22, 19, 17,
    8, 10, 13, 15, 12, 11, 0, 24, 1, 20, 26, 6, 5]

def later (i : Fin 21) : Fin 27 := ⟨i.val + 6, by omega⟩

def predecessors : Fin 21 → Fin 27 × Fin 27 :=
  ![(0, 4), (1, 3), (1, 5), (1, 4), (2, 7), (2, 8), (2, 9),
    (2, 6), (10, 5), (10, 4), (14, 13), (14, 9), (3, 6), (15, 13),
    (17, 7), (20, 13), (16, 7), (22, 11), (0, 14), (1, 24), (2, 24)]

def triple (i : Fin 21) : Fin 27 × Fin 27 × Fin 27 :=
  (coordinateOrder (later i), coordinateOrder (predecessors i).1,
    coordinateOrder (predecessors i).2)

def tripleCoefficient : Fin 21 → ℤ :=
  ![-1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1, -1, 1, -1, 1]

theorem coefficient_ne_zero (i : Fin 21) : tripleCoefficient i ≠ 0 := by decide +kernel +revert

theorem predecessors_lt (i : Fin 21) :
    (predecessors i).1 < later i ∧ (predecessors i).2 < later i := by decide +kernel +revert

theorem coordinateOrder_seed (i : Fin 6) :
    coordinateOrder ⟨i.val, by omega⟩ = seed i := by decide +kernel +revert

theorem coordinateOrder_surjective : Function.Surjective coordinateOrder := by decide +kernel

def tripleMask (i : Fin 21) (d : Fin 27 → ℂ) : Fin 27 → ℂ :=
  fun a => if a = (triple i).1 ∨ a = (triple i).2.1 ∨ a = (triple i).2.2 then d a else 0

private theorem eval_mask (p : SparseCubicCertificate.Code (Fin 27))
    (s : Fin 27 → Prop) [DecidablePred s] (d : Fin 27 → ℂ) :
    SparseCubicCertificate.eval p (fun a => if s a then d a else 0) =
      SparseCubicCertificate.eval
        (p.filter fun e => decide (s e.1.1 ∧ s e.1.2.1 ∧ s e.1.2.2)) d := by
  induction p with
  | nil => rfl
  | cons e es ih =>
    by_cases h₁ : s e.1.1 <;> by_cases h₂ : s e.1.2.1 <;> by_cases h₃ : s e.1.2.2 <;>
      simp [SparseCubicCertificate.eval, SparseCubicCertificate.value, ih, h₁, h₂, h₃]

private theorem cubic_mask_checked (i : Fin 21) :
    cubicCode.filter (fun e => decide
      ((e.1.1 = (triple i).1 ∨ e.1.1 = (triple i).2.1 ∨ e.1.1 = (triple i).2.2) ∧
       (e.1.2.1 = (triple i).1 ∨ e.1.2.1 = (triple i).2.1 ∨ e.1.2.1 = (triple i).2.2) ∧
       (e.1.2.2 = (triple i).1 ∨ e.1.2.2 = (triple i).2.1 ∨ e.1.2.2 = (triple i).2.2))) =
      [(SparseCubicCertificate.sortTriple (triple i), tripleCoefficient i)] := by
  decide +kernel +revert

theorem cubic_tripleMask (i : Fin 21) (d : Fin 27 → ℂ) :
    cubic (tripleMask i d) = (tripleCoefficient i : ℂ) *
      d (triple i).1 * d (triple i).2.1 * d (triple i).2.2 := by
  unfold cubic tripleMask
  rw [eval_mask, cubic_mask_checked]
  simp only [SparseCubicCertificate.eval, add_zero]
  exact SparseCubicCertificate.value_sort (triple i, tripleCoefficient i) d

theorem diagonal_triple_relation (g : compactIdentityComponent) (d : Fin 27 → Circle)
    (hg : compactMatrix g = Matrix.diagonal (fun a => (d a : ℂ))) (i : Fin 21) :
    d (triple i).1 * d (triple i).2.1 * d (triple i).2.2 = 1 := by
  have h := cubic_invariant g (tripleMask i (fun _ => 1))
  have hm : compactMatrix g *ᵥ tripleMask i (fun _ => 1) =
      tripleMask i (fun a => (d a : ℂ)) := by
    rw [hg]
    ext a
    simp only [Matrix.mulVec_diagonal, tripleMask]
    split_ifs <;> simp
  rw [hm, cubic_tripleMask, cubic_tripleMask] at h
  have hc : (tripleCoefficient i : ℂ) ≠ 0 := by exact_mod_cast coefficient_ne_zero i
  apply Circle.coe_injective
  simp only [Circle.coe_mul, Circle.coe_one]
  apply mul_left_cancel₀ hc
  simpa only [mul_one, mul_assoc] using h

theorem eq_of_triples (d e : Fin 27 → Circle)
    (hd : ∀ i, d (triple i).1 * d (triple i).2.1 * d (triple i).2.2 = 1)
    (he : ∀ i, e (triple i).1 * e (triple i).2.1 * e (triple i).2.2 = 1)
    (hs : ∀ i, d (seed i) = e (seed i)) : d = e := by
  have hall (i : Fin 27) : d (coordinateOrder i) = e (coordinateOrder i) := by
    induction i using WellFounded.induction (measure Fin.val).wf with
    | h i ih =>
      by_cases hi : i.val < 6
      · have h := hs ⟨i.val, hi⟩
        simpa only [← coordinateOrder_seed] using h
      · let j : Fin 21 := ⟨i.val - 6, by omega⟩
        have hj : later j = i := by ext; dsimp [later, j]; omega
        have hl := ih (predecessors j).1 (hj ▸ (predecessors_lt j).1)
        have hr := ih (predecessors j).2 (hj ▸ (predecessors_lt j).2)
        have h := (hd j).trans (he j).symm
        change (d (coordinateOrder (later j)) * d (coordinateOrder (predecessors j).1)) *
          d (coordinateOrder (predecessors j).2) =
          (e (coordinateOrder (later j)) * e (coordinateOrder (predecessors j).1)) *
          e (coordinateOrder (predecessors j).2) at h
        rw [hj, hl, hr] at h
        exact mul_right_cancel (mul_right_cancel h)
  funext a
  obtain ⟨i, rfl⟩ := coordinateOrder_surjective a
  exact hall i

theorem diagonal_reconstruction (g : compactIdentityComponent) (d : Fin 27 → Circle)
    (hg : compactMatrix g = Matrix.diagonal (fun a => (d a : ℂ))) :
    g = hom (recover d) := by
  have he : d = weights (recover d) := eq_of_triples d _
    (diagonal_triple_relation g d hg)
    (diagonal_triple_relation (hom (recover d)) _ (hom_matrix _))
    (fun i => (weights_recover_seed d i).symm)
  apply compactMatrix_injective
  rw [hg, hom_matrix]
  conv_lhs => rw [he]
  rfl

end

end Math.E6.Minuscule.Torus
