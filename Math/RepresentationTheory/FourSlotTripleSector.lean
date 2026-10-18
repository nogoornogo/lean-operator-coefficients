import Math.RepresentationTheory.FourSlotTripleAlternation

/-! Intrinsic pure-species support for the (3,1) exterior sector. This is not
defined as the image of a contraction or an alternatization map. -/
namespace Math.FourSlotTripleSector
set_option autoImplicit false
noncomputable section
open Representation FourSlotTripleAlternation
open scoped TensorProduct
variable {H A B : Type*} [Group H] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

def project (i : Fin 2) (v : A × B) : A × B := if i = 0 then (v.1, 0) else (0, v.2)

omit [Module ℂ A] [Module ℂ B] in
theorem sum_project (v : A × B) : ∑ i : Fin 2, project i v = v := by
  simp [project, Fin.sum_univ_two]

def HasPattern (labels : Fin 4 → Fin 2) : Prop :=
  ∃ p : Equiv.Perm (Fin 4), labels ∘ p = ![0,0,0,1]

variable (a : Representation ℂ H A) (b : Representation ℂ H B)
abbrev Coefficient := IntertwiningMap ((a.prod b).exteriorPower 4) (Representation.trivial ℂ H ℂ)

def evaluation (f : Coefficient a b) : (A × B) [⋀^Fin 4]→ₗ[ℂ] ℂ :=
  f.toLinearMap.compAlternatingMap (exteriorPower.ιMulti ℂ 4)

def HasDegree (f : Coefficient a b) : Prop := ∀ labels, ¬ HasPattern labels →
  ∀ v : Fin 4 → A × B, evaluation a b f (fun i => project (labels i) (v i)) = 0

def sector : Submodule ℂ (Coefficient a b) where
  carrier := {f | HasDegree a b f}
  zero_mem' := by intro labels hl v; rfl
  add_mem' := by
    intro f g hf hg labels hl v
    change evaluation a b f _ + evaluation a b g _ = 0
    rw [hf labels hl v, hg labels hl v, add_zero]
  smul_mem' := by
    intro z f hf labels hl v
    change z • evaluation a b f _ = 0
    rw [hf labels hl v, smul_zero]

theorem eq_zero_of_slots (f : Coefficient a b) (hf : HasDegree a b f)
    (hs : ∀ x y z h, f (exteriorPower.ιMulti ℂ 4 (slots x y z h)) = 0) : f = 0 := by
  have hpure (labels : Fin 4 → Fin 2) (v : Fin 4 → A × B) :
      evaluation a b f (fun i => project (labels i) (v i)) = 0 := by
    by_cases hl : HasPattern labels
    · obtain ⟨p, hp⟩ := hl
      have h0 : labels (p 0) = 0 := congrFun hp 0
      have h1 : labels (p 1) = 0 := congrFun hp 1
      have h2 : labels (p 2) = 0 := congrFun hp 2
      have h3 : labels (p 3) = 1 := congrFun hp 3
      have hv : (fun i => project (labels i) (v i)) ∘ p =
          slots (v (p 0)).1 (v (p 1)).1 (v (p 2)).1 (v (p 3)).2 := by
        funext i
        fin_cases i <;> simp [project, slots, h0, h1, h2, h3]
      have he := (evaluation a b f).map_congr_perm (fun i => project (labels i) (v i)) p
      rw [hv] at he
      have hz : evaluation a b f (slots (v (p 0)).1 (v (p 1)).1 (v (p 2)).1 (v (p 3)).2) = 0 :=
        hs _ _ _ _
      rw [hz, smul_zero] at he
      exact he
    · exact hf labels hl v
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  change evaluation a b f v = 0
  calc
    _ = evaluation a b f (fun i => ∑ j : Fin 2, project j (v i)) := by simp only [sum_project]
    _ = ∑ labels : Fin 4 → Fin 2, evaluation a b f (fun i => project (labels i) (v i)) :=
      (evaluation a b f).toMultilinearMap.map_sum (fun i j => project j (v i))
    _ = 0 := Finset.sum_eq_zero (fun labels _ => hpure labels v)

theorem slots_ext (f g : Coefficient a b) (hf : HasDegree a b f) (hg : HasDegree a b g)
    (hs : ∀ x y z h, f (exteriorPower.ιMulti ℂ 4 (slots x y z h)) =
      g (exteriorPower.ιMulti ℂ 4 (slots x y z h))) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_slots a b (f - g) ((sector a b).sub_mem hf hg)
  intro x y z h
  change f _ - g _ = 0
  exact sub_eq_zero.mpr (hs x y z h)

theorem coefficient_hasDegree (f : IntertwiningMap ((a.tprod a).tprod (a.tprod b))
    (Representation.trivial ℂ H ℂ)) : HasDegree a b (coefficient a b f) := by
  intro labels hl v
  change exteriorPower.alternatingMapLinearEquiv (alternating f.toLinearMap)
    (exteriorPower.ιMulti ℂ 4 (fun i => project (labels i) (v i))) = 0
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [alternating, MultilinearMap.alternatization_apply]
  apply Finset.sum_eq_zero
  intro p _
  have hn : ¬ (labels (p 0) = 0 ∧ labels (p 1) = 0 ∧ labels (p 2) = 0 ∧ labels (p 3) = 1) := by
    rintro ⟨h0,h1,h2,h3⟩
    apply hl
    refine ⟨p, ?_⟩
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  by_cases h0 : labels (p 0) = 0
  · by_cases h1 : labels (p 1) = 0
    · by_cases h2 : labels (p 2) = 0
      · have h3 : labels (p 3) = 0 := by
          have hn3 : labels (p 3) ≠ 1 := fun h => hn ⟨h0,h1,h2,h⟩
          have hnlt := (labels (p 3)).isLt
          apply Fin.ext
          have hval : (labels (p 3)).val ≠ 1 := fun he => hn3 (Fin.ext he)
          omega
        simp [MultilinearMap.domDomCongr_apply, ordered, project, h3]
      · simp [MultilinearMap.domDomCongr_apply, ordered, project, h2]
    · simp [MultilinearMap.domDomCongr_apply, ordered, project, h1]
  · simp [MultilinearMap.domDomCongr_apply, ordered, project, h0]

end
end Math.FourSlotTripleSector
