import Math.RepresentationTheory.Content.MixedSingleSpeciesProjection

/-! Two-sided finite support partition for one-boson independent coefficients. -/
namespace Math.MixedSingleSpeciesPartition
set_option autoImplicit false
noncomputable section
open Representation FiniteSpeciesExterior MixedSingleSpeciesProjection
variable {P Q G I : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Fintype I] [DecidableEq I]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))
  {n : ℕ} (ps : I → (Fin n → P) → Q → Prop)
  [∀ i labels, DecidablePred (ps i labels)]
  (stable : ∀ i labels u (p : Equiv.Perm (Fin n)), ps i (labels ∘ p) u ↔ ps i labels u)
  (disjoint : ∀ i j, i ≠ j → ∀ labels u, ps i labels u → ¬ ps j labels u)

abbrev partitionSpace : Submodule ℂ (Coefficient r t (n := n)) :=
  supportSpace r t (fun labels u => ∃ i, ps i labels u)

def split (f : partitionSpace r t ps) : ∀ i, supportSpace r t (ps i) :=
  fun i => ⟨project r t (ps i) f.val, project_mem r t (ps i) (stable i) f.val⟩

def join (f : ∀ i, supportSpace r t (ps i)) : partitionSpace r t ps :=
  ⟨∑ i, (f i).val, by
    intro labels u v w hout
    change (∑ i, (f i).val) (MixedWeightSupport.pure
      (fun i => Pi.single (labels i) (v i)) (fun _ : Fin 1 => Pi.single u w)) = 0
    rw [IntertwiningMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    exact (f i).property labels u v w (fun hi => hout ⟨i, hi⟩)⟩

omit [DecidableEq I] in
include disjoint in
theorem split_join (f : ∀ i, supportSpace r t (ps i)) : split r t ps stable (join r t ps f) = f := by
  funext i
  apply Subtype.ext
  apply coefficient_ext r t
  intro labels u v w
  change project r t (ps i) (∑ j, (f j).val) _ = (f i).val _
  rw [project_pure r t (ps i) (stable i)]
  by_cases hi : ps i labels u
  · rw [ite_eq_left hi, IntertwiningMap.sum_apply, Finset.sum_eq_single i]
    · intro j _ hji
      exact (f j).property labels u v w (disjoint i j (Ne.symm hji) labels u hi)
    · simp
  · rw [ite_eq_right hi, (f i).property labels u v w hi]

omit [DecidableEq I] in
include disjoint in
theorem join_split (f : partitionSpace r t ps) : join r t ps (split r t ps stable f) = f := by
  apply Subtype.ext
  apply coefficient_ext r t
  intro labels u v w
  change (∑ i, project r t (ps i) f.val) _ = f.val _
  rw [IntertwiningMap.sum_apply]
  simp only [project_pure r t _ (stable _)]
  by_cases hh : ∃ i, ps i labels u
  · obtain ⟨i, hi⟩ := hh
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left hi]
    · intro j _ hji
      exact ite_eq_right (disjoint i j (Ne.symm hji) labels u hi)
    · simp
  · rw [f.property labels u v w hh]
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hh ⟨i, hi⟩)

def equiv : partitionSpace r t ps ≃ₗ[ℂ] (∀ i, supportSpace r t (ps i)) where
  toFun := split r t ps stable
  invFun := join r t ps
  left_inv := join_split r t ps stable disjoint
  right_inv := split_join r t ps stable disjoint
  map_add' f h := by
    funext i
    apply Subtype.ext
    exact (projectLinear r t (ps i) (stable i)).map_add f.val h.val
  map_smul' z f := by
    funext i
    apply Subtype.ext
    exact (projectLinear r t (ps i) (stable i)).map_smul z f.val

/-- Transfer the partition equivalence before specializing the field carriers. -/
def equivOfEq (A : Submodule ℂ (Coefficient r t (n := n)))
    (he : A = partitionSpace r t ps) : A ≃ₗ[ℂ] (∀ i, supportSpace r t (ps i)) :=
  (LinearEquiv.ofEq _ _ he).trans (equiv r t ps stable disjoint)

end
end Math.MixedSingleSpeciesPartition
