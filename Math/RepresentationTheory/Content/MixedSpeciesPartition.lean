import Math.RepresentationTheory.Content.MixedSpeciesProjection

/-! Finite species-support decomposition at arbitrary fermion and boson degrees. -/
namespace Math.MixedSpeciesPartition
set_option autoImplicit false
noncomputable section
open Representation FiniteSpeciesExterior MixedSpeciesProjection
variable {P Q G I : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Fintype I] [DecidableEq I]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))
  {n m : ℕ} (ps : I → (Fin n → P) → (Fin m → Q) → Prop)
  [∀ i labels scalars, Decidable (ps i labels scalars)]
  (stable : ∀ i labels scalars (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)),
    ps i (labels ∘ p) (scalars ∘ q) ↔ ps i labels scalars)
  (disjoint : ∀ i j, i ≠ j → ∀ labels scalars,
    ps i labels scalars → ¬ ps j labels scalars)

abbrev partitionSpace : Submodule ℂ (Coefficient r t (n := n) (m := m)) :=
  supportSpace (fun labels scalars => ∃ i, ps i labels scalars) r t

def split (f : partitionSpace r t ps) : ∀ i, supportSpace (ps i) r t :=
  fun i => ⟨invariantProject (ps i) (stable i) r t f.val,
    project_mem (ps i) (stable i) r t f.val⟩

def join (f : ∀ i, supportSpace (ps i) r t) : partitionSpace r t ps :=
  ⟨∑ i, (f i).val, by
    intro labels scalars hout v w
    rw [IntertwiningMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    exact (f i).property labels scalars (fun hi => hout ⟨i, hi⟩) v w⟩

omit [DecidableEq I] in
include disjoint in
theorem split_join (f : ∀ i, supportSpace (ps i) r t) :
    split r t ps stable (join r t ps f) = f := by
  funext i
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply MixedSpeciesExt.ext
  intro labels scalars v w
  change project (ps i) (∑ j, (f j).val).toLinearMap _ = (f i).val _
  rw [project_pure (ps i) (stable i)]
  by_cases hi : ps i labels scalars
  · rw [ite_eq_left hi]
    change (∑ j, (f j).val) _ = (f i).val _
    rw [IntertwiningMap.sum_apply, Finset.sum_eq_single i]
    · intro j _ hji
      exact (f j).property labels scalars
        (disjoint i j (Ne.symm hji) labels scalars hi) v w
    · simp
  · rw [ite_eq_right hi, (f i).property labels scalars hi v w]

omit [DecidableEq I] in
include disjoint in
theorem join_split (f : partitionSpace r t ps) :
    join r t ps (split r t ps stable f) = f := by
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply MixedSpeciesExt.ext
  intro labels scalars v w
  change (∑ i, invariantProject (ps i) (stable i) r t f.val) _ = f.val _
  rw [IntertwiningMap.sum_apply]
  change (∑ i, project (ps i) f.val.toLinearMap _) = f.val _
  simp only [project_pure (ps _) (stable _)]
  by_cases hh : ∃ i, ps i labels scalars
  · obtain ⟨i, hi⟩ := hh
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left hi]
      rfl
    · intro j _ hji
      exact ite_eq_right (disjoint i j (Ne.symm hji) labels scalars hi)
    · simp
  · rw [f.property labels scalars hh v w]
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hh ⟨i, hi⟩)

def equiv : partitionSpace r t ps ≃ₗ[ℂ] (∀ i, supportSpace (ps i) r t) where
  toFun := split r t ps stable
  invFun := join r t ps
  left_inv := join_split r t ps stable disjoint
  right_inv := split_join r t ps stable disjoint
  map_add' f h := by
    funext i
    apply Subtype.ext
    exact (projectLinear (ps i) (stable i) r t).map_add f.val h.val
  map_smul' z f := by
    funext i
    apply Subtype.ext
    exact (projectLinear (ps i) (stable i) r t).map_smul z f.val

end
end Math.MixedSpeciesPartition
