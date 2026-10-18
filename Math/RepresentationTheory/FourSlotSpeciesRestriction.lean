import Math.RepresentationTheory.FourSlotSpeciesDegree

/-! Degree (2,1,1) exterior coefficients are determined by their ordered slots.
The weights 2,3,5 separate all species counts in degree four. -/
namespace Math.FourSlotSpeciesRestriction
set_option autoImplicit false
noncomputable section
open Representation FourSlotAlternation FourSlotSpeciesDegree
open scoped TensorProduct

variable {H A B C : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

def project (i : Fin 3) (v : Fields A B C) : Fields A B C :=
  (![ (v.1, 0, 0), (0, v.2.1, 0), (0, 0, v.2.2)] : Fin 3 → Fields A B C) i

omit [Module ℂ A] [Module ℂ B] [Module ℂ C] in
theorem sum_project (v : Fields A B C) : ∑ i : Fin 3, project i v = v := by
  ext <;> simp [project, Fin.sum_univ_succ]

private def weight : Fin 3 → ℕ := ![2, 3, 5]

private theorem label_permutation (l : Fin 4 → Fin 3) (h : ∏ i, weight (l i) = 60) :
    ∃ p : Equiv.Perm (Fin 4), l ∘ p = ![0, 0, 1, 2] := by
  have finite_check : ∀ l : Fin 4 → Fin 3, (∏ i, weight (l i)) = 60 →
      ∃ p : Equiv.Perm (Fin 4), l ∘ p = ![0, 0, 1, 2] := by decide +kernel
  exact finite_check l h

variable (a : Representation ℂ H A) (b : Representation ℂ H B) (c : Representation ℂ H C)

def evaluation (f : coefficients a b c) : Fields A B C [⋀^Fin 4]→ₗ[ℂ] ℂ :=
  f.toLinearMap.compAlternatingMap (exteriorPower.ιMulti ℂ 4)

private theorem scaling_project (i : Fin 3) (v : Fields A B C) :
    scaling a b c 2 3 5 (project i v) = (weight i : ℂ) • project i v := by
  fin_cases i <;> simp [scaling, project, weight]

theorem vanish_wrong_degree (f : coefficients a b c) (hf : HasDegree a b c f)
    (l : Fin 4 → Fin 3) (v : Fin 4 → Fields A B C)
    (hl : (∏ i, weight (l i)) ≠ 60) :
    evaluation a b c f (fun i => project (l i) (v i)) = 0 := by
  have h := hf 2 3 5 (exteriorPower.ιMulti ℂ 4 (fun i => project (l i) (v i)))
  rw [IntertwiningMap.exteriorPower_apply_ιMulti] at h
  change evaluation a b c f (fun i => scaling a b c 2 3 5 (project (l i) (v i))) =
    (2 * 2 * 3 * 5 : ℂ) • evaluation a b c f (fun i => project (l i) (v i)) at h
  simp_rw [scaling_project] at h
  have hm := (evaluation a b c f).toMultilinearMap.map_smul_univ
    (fun i => (weight (l i) : ℂ)) (fun i => project (l i) (v i))
  have h' := hm.symm.trans h
  have hn : ((∏ i, weight (l i) : ℕ) : ℂ) ≠ 60 := by exact_mod_cast hl
  have hz : (((∏ i, weight (l i) : ℕ) : ℂ) - 60) *
      evaluation a b c f (fun i => project (l i) (v i)) = 0 := by
    push_cast at h' ⊢
    simp only [smul_eq_mul] at h'
    linear_combination h'
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

theorem eq_zero_of_slots (f : coefficients a b c) (hf : HasDegree a b c f)
    (hs : ∀ x y u e, f (exteriorPower.ιMulti ℂ 4 (slots x y u e)) = 0) : f = 0 := by
  have hpure (l : Fin 4 → Fin 3) (v : Fin 4 → Fields A B C) :
      evaluation a b c f (fun i => project (l i) (v i)) = 0 := by
    by_cases hl : (∏ i, weight (l i)) = 60
    · obtain ⟨p, hp⟩ := label_permutation l hl
      have h0 : l (p 0) = 0 := congrFun hp 0
      have h1 : l (p 1) = 0 := congrFun hp 1
      have h2 : l (p 2) = 1 := congrFun hp 2
      have h3 : l (p 3) = 2 := congrFun hp 3
      have hw : (fun i => project (l i) (v i)) ∘ p =
          slots (v (p 0)).1 (v (p 1)).1 (v (p 2)).2.1 (v (p 3)).2.2 := by
        funext i
        fin_cases i <;> simp [h0, h1, h2, h3, project, slots]
      have he := (evaluation a b c f).map_congr_perm (fun i => project (l i) (v i)) p
      rw [hw] at he
      have hz : evaluation a b c f
          (slots (v (p 0)).1 (v (p 1)).1 (v (p 2)).2.1 (v (p 3)).2.2) = 0 :=
        hs _ _ _ _
      rw [hz, smul_zero] at he
      exact he
    · exact vanish_wrong_degree a b c f hf l v hl
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  change evaluation a b c f v = 0
  calc
    evaluation a b c f v = evaluation a b c f (fun i => ∑ j : Fin 3, project j (v i)) := by
      simp only [sum_project]
    _ = ∑ l : Fin 4 → Fin 3, evaluation a b c f (fun i => project (l i) (v i)) :=
      (evaluation a b c f).toMultilinearMap.map_sum (fun i j => project j (v i))
    _ = 0 := Finset.sum_eq_zero (fun l _ => hpure l v)

theorem slots_ext (f g : coefficients a b c) (hf : HasDegree a b c f)
    (hg : HasDegree a b c g)
    (hs : ∀ x y u e, f (exteriorPower.ιMulti ℂ 4 (slots x y u e)) =
      g (exteriorPower.ιMulti ℂ 4 (slots x y u e))) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_slots a b c (f - g) ((sector a b c).sub_mem hf hg)
  intro x y u e
  change f _ - g _ = 0
  exact sub_eq_zero.mpr (hs x y u e)

end
end Math.FourSlotSpeciesRestriction
