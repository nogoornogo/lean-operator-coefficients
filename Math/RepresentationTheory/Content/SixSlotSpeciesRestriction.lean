import Math.RepresentationTheory.Content.SixSlotSpeciesDegree

/-! A degree `(2,4)` exterior coefficient is determined by its ordered
`(A,B,A,B,B,B)` slots.  The weights `2,3` separate the seven bidegrees in
total degree six. -/
namespace Math.SixSlotSpeciesRestriction

set_option autoImplicit false
noncomputable section

open Representation SixSlotAlternation SixSlotSpeciesDegree

variable {H A B : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

def project (i : Fin 2) (v : Fields A B) : Fields A B :=
  (![ (v.1, 0), (0, v.2)] : Fin 2 → Fields A B) i

omit [Module ℂ A] [Module ℂ B] in
theorem sum_project (v : Fields A B) : ∑ i : Fin 2, project i v = v := by
  ext <;> simp [project, Fin.sum_univ_succ]

private def weight : Fin 2 → ℕ := ![2, 3]

private theorem label_permutation (l : Fin 6 → Fin 2)
    (h : ∏ i, weight (l i) = 324) :
    ∃ p : Equiv.Perm (Fin 6), l ∘ p = ![0, 1, 0, 1, 1, 1] := by
  have finite_check : ∀ l : Fin 6 → Fin 2, (∏ i, weight (l i)) = 324 →
      ∃ p : Equiv.Perm (Fin 6), l ∘ p = ![0, 1, 0, 1, 1, 1] := by decide +kernel
  exact finite_check l h

variable (a : Representation ℂ H A) (b : Representation ℂ H B)

def evaluation (f : coefficients a b) : Fields A B [⋀^Fin 6]→ₗ[ℂ] ℂ :=
  f.toLinearMap.compAlternatingMap (exteriorPower.ιMulti ℂ 6)

@[simp] theorem evaluation_apply (f : coefficients a b) (v : Fin 6 → Fields A B) :
    evaluation a b f v = f (exteriorPower.ιMulti ℂ 6 v) := rfl

/-- Invariant alternating evaluation descends through the exterior universal property. -/
def ofEvaluation (ev : Fields A B [⋀^Fin 6]→ₗ[ℂ] ℂ)
    (hinv : ∀ h v, ev (fun i => action a b h (v i)) = ev v) : coefficients a b where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv ev
  isIntertwining' h := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact hinv h v

@[simp] theorem ofEvaluation_apply (ev : Fields A B [⋀^Fin 6]→ₗ[ℂ] ℂ)
    (hinv : ∀ h v, ev (fun i => action a b h (v i)) = ev v)
    (v : Fin 6 → Fields A B) :
    ofEvaluation a b ev hinv (exteriorPower.ιMulti ℂ 6 v) = ev v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem ofEvaluation_degree (ev : Fields A B [⋀^Fin 6]→ₗ[ℂ] ℂ)
    (hinv : ∀ h v, ev (fun i => action a b h (v i)) = ev v)
    (hscale : ∀ r s v, ev (fun i => scaling a b r s (v i)) =
      (r * r * s * s * s * s) • ev v) : HasDegree a b (ofEvaluation a b ev hinv) := by
  intro r s
  suffices he : (ofEvaluation a b ev hinv).toLinearMap.comp
      ((scaling a b r s).exteriorPower 6).toLinearMap =
      (r * r * s * s * s * s) • (ofEvaluation a b ev hinv).toLinearMap by
    intro v
    exact LinearMap.congr_fun he v
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    IntertwiningMap.toLinearMap_apply, IntertwiningMap.exteriorPower_apply_ιMulti,
    ofEvaluation_apply, LinearMap.smul_apply]
  exact hscale r s v

private theorem scaling_project (i : Fin 2) (v : Fields A B) :
    scaling a b 2 3 (project i v) = (weight i : ℂ) • project i v := by
  fin_cases i <;> simp [scaling, project, weight]

theorem vanish_wrong_degree (f : coefficients a b) (hf : HasDegree a b f)
    (l : Fin 6 → Fin 2) (v : Fin 6 → Fields A B)
    (hl : (∏ i, weight (l i)) ≠ 324) :
    evaluation a b f (fun i => project (l i) (v i)) = 0 := by
  have h := hf 2 3 (exteriorPower.ιMulti ℂ 6 (fun i => project (l i) (v i)))
  rw [IntertwiningMap.exteriorPower_apply_ιMulti] at h
  change evaluation a b f (fun i => scaling a b 2 3 (project (l i) (v i))) =
    (2 * 2 * 3 * 3 * 3 * 3 : ℂ) •
      evaluation a b f (fun i => project (l i) (v i)) at h
  simp_rw [scaling_project] at h
  have hm := (evaluation a b f).toMultilinearMap.map_smul_univ
    (fun i => (weight (l i) : ℂ)) (fun i => project (l i) (v i))
  have h' := hm.symm.trans h
  have hn : (((∏ i, weight (l i) : ℕ) : ℂ) ≠ 324) := by exact_mod_cast hl
  have hz : (((∏ i, weight (l i) : ℕ) : ℂ) - 324) *
      evaluation a b f (fun i => project (l i) (v i)) = 0 := by
    push_cast at h' ⊢
    simp only [smul_eq_mul] at h'
    linear_combination h'
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

theorem eq_zero_of_slots (f : coefficients a b) (hf : HasDegree a b f)
    (hs : ∀ u₁ u₂ d₁ d₂ d₃ d₄,
      f (exteriorPower.ιMulti ℂ 6 (slots u₁ u₂ d₁ d₂ d₃ d₄)) = 0) :
    f = 0 := by
  have hpure (l : Fin 6 → Fin 2) (v : Fin 6 → Fields A B) :
      evaluation a b f (fun i => project (l i) (v i)) = 0 := by
    by_cases hl : (∏ i, weight (l i)) = 324
    · obtain ⟨p, hp⟩ := label_permutation l hl
      have h0 : l (p 0) = 0 := congrFun hp 0
      have h1 : l (p 1) = 1 := congrFun hp 1
      have h2 : l (p 2) = 0 := congrFun hp 2
      have h3 : l (p 3) = 1 := congrFun hp 3
      have h4 : l (p 4) = 1 := congrFun hp 4
      have h5 : l (p 5) = 1 := congrFun hp 5
      have hw : (fun i => project (l i) (v i)) ∘ p =
          slots (v (p 0)).1 (v (p 2)).1 (v (p 1)).2
            (v (p 3)).2 (v (p 4)).2 (v (p 5)).2 := by
        funext i
        fin_cases i <;> simp [h0, h1, h2, h3, h4, h5, project, slots]
      have he := (evaluation a b f).map_congr_perm
        (fun i => project (l i) (v i)) p
      rw [hw] at he
      have hz := hs (v (p 0)).1 (v (p 2)).1 (v (p 1)).2
        (v (p 3)).2 (v (p 4)).2 (v (p 5)).2
      change evaluation a b f
        (slots (v (p 0)).1 (v (p 2)).1 (v (p 1)).2
          (v (p 3)).2 (v (p 4)).2 (v (p 5)).2) = 0 at hz
      rw [hz, smul_zero] at he
      exact he
    · exact vanish_wrong_degree a b f hf l v hl
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  change evaluation a b f v = 0
  calc
    evaluation a b f v =
        evaluation a b f (fun i => ∑ j : Fin 2, project j (v i)) := by
          simp only [sum_project]
    _ = ∑ l : Fin 6 → Fin 2, evaluation a b f (fun i => project (l i) (v i)) :=
      (evaluation a b f).toMultilinearMap.map_sum (fun i j => project j (v i))
    _ = 0 := Finset.sum_eq_zero (fun l _ => hpure l v)

theorem slots_ext (f g : coefficients a b) (hf : HasDegree a b f)
    (hg : HasDegree a b g)
    (hs : ∀ u₁ u₂ d₁ d₂ d₃ d₄,
      f (exteriorPower.ιMulti ℂ 6 (slots u₁ u₂ d₁ d₂ d₃ d₄)) =
      g (exteriorPower.ιMulti ℂ 6 (slots u₁ u₂ d₁ d₂ d₃ d₄))) :
    f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_slots a b (f - g) ((sector a b).sub_mem hf hg)
  intro u₁ u₂ d₁ d₂ d₃ d₄
  change f _ - g _ = 0
  exact sub_eq_zero.mpr (hs u₁ u₂ d₁ d₂ d₃ d₄)

/-- Sector extensionality phrased entirely through alternating evaluation. -/
theorem sector_ext (f g : ↥(sector a b))
    (hs : ∀ u₁ u₂ d₁ d₂ d₃ d₄,
      evaluation a b f.val (slots u₁ u₂ d₁ d₂ d₃ d₄) =
      evaluation a b g.val (slots u₁ u₂ d₁ d₂ d₃ d₄)) : f = g := by
  apply Subtype.ext
  exact slots_ext a b f.val g.val f.property g.property hs

/-- Alternatization on species slots is normalized by the stabilizer order,
provided the wrong species placements vanish and the correct ones have the sign law. -/
theorem alternatization_slots
    (f : MultilinearMap ℂ (fun _ : Fin 6 => Fields A B) ℂ)
    (v : Fin 6 → Fields A B)
    (hgood : ∀ p : Equiv.Perm (Fin 6), PreservesPattern p →
      f (v ∘ p) = Equiv.Perm.sign p • f v)
    (hbad : ∀ p : Equiv.Perm (Fin 6), ¬ PreservesPattern p → f (v ∘ p) = 0) :
    f.alternatization v = 48 • f v := by
  classical
  rw [MultilinearMap.alternatization_apply]
  let good := Finset.univ.filter PreservesPattern
  rw [← Finset.sum_subset (show good ⊆ Finset.univ from Finset.subset_univ _)]
  · calc
      ∑ p ∈ good, Equiv.Perm.sign p • f (v ∘ p) = ∑ _p ∈ good, f v := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hgood p (Finset.mem_filter.mp hp).2, smul_smul]
        simp
      _ = 48 • f v := by
        rw [Finset.sum_const, nsmul_eq_mul, preservesPattern_card]
        norm_num
  · intro p _ hp
    change Equiv.Perm.sign p • f (v ∘ p) = 0
    rw [hbad p (by simpa [good] using hp), smul_zero]

end
end Math.SixSlotSpeciesRestriction
