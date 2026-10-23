import Math.Algebra.Jets.MixedJetGrading
import Math.Algebra.Constructions.ScalarDegreeTwo

/-! The entire first-derivative mixed grade is spanned by words with one
marked derivative slot. This does not restrict the field labels or statistics. -/
namespace Math.MixedFirstJetWords
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MixedJetAlgebra
attribute [local instance] Classical.propDecidable
variable {F B I : Type*} {n m : ℕ}

def first (f : Fin n → F) (b : Fin m → B) (t : Fin n ⊕ Fin m) (i : I) :
    Algebra F B I := word
      (fun j => (f j,if Sum.inl j = t then Finsupp.single i 1 else 0))
      (fun j => (b j,if Sum.inr j = t then Finsupp.single i 1 else 0))

def orders (f : Fin n → Index F I) (b : Fin m → Index B I) :
    (Fin n ⊕ Fin m) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun j => order (f j).2) (fun j => order (b j).2))

theorem orders_sum (f : Fin n → Index F I) (b : Fin m → Index B I) :
    (orders f b).sum (fun _ k => k) = wordOrder f b := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp [orders,wordOrder,Fintype.sum_sum_type]

theorem word_eq_first (f : Fin n → Index F I) (b : Fin m → Index B I)
    (h : wordOrder f b = 1) :
    ∃ t i, word f b = first (fun j => (f j).1) (fun j => (b j).1) t i := by
  classical
  have hs : (orders f b).sum (fun _ k => k) = 1 := (orders_sum f b).trans h
  obtain ⟨t,ht⟩ := (Finsupp.sum_eq_one_iff _).mp hs
  have ho (s : Fin n ⊕ Fin m) :
      Sum.elim (fun j => order (f j).2) (fun j => order (b j).2) s =
        if s = t then 1 else 0 := by
    simpa [orders,Finsupp.single_apply,eq_comm] using DFunLike.congr_fun ht s
  have selected : ∃ i, Sum.elim (fun j => (f j).2) (fun j => (b j).2) t = Finsupp.single i 1 := by
    apply ScalarDegreeTwo.order_one
    cases t with
    | inl j => simpa using ho (.inl j)
    | inr j => simpa using ho (.inr j)
  obtain ⟨i,hi⟩ := selected
  have he (s : Fin n ⊕ Fin m) :
      Sum.elim (fun j => (f j).2) (fun j => (b j).2) s =
        if s = t then Finsupp.single i 1 else 0 := by
    by_cases hst : s = t
    · simpa [hst] using hi
    · simp only [hst,ite_false]
      apply ScalarDegreeTwo.order_zero
      cases s with
      | inl j => simpa [hst] using ho (.inl j)
      | inr j => simpa [hst] using ho (.inr j)
  refine ⟨t,i,?_⟩
  unfold first
  congr 1
  · funext j
    exact Prod.ext rfl (he (.inl j))
  · funext j
    exact Prod.ext rfl (he (.inr j))

theorem grade_le_span : grade F B I n m 1 ≤
    Submodule.span ℂ {p | ∃ (f : Fin n → F) (b : Fin m → B)
      (t : Fin n ⊕ Fin m) (i : I), first f b t i = p} := by
  apply Submodule.span_le.mpr
  rintro p ⟨f,b,h,rfl⟩
  obtain ⟨t,i,he⟩ := word_eq_first f b h
  exact Submodule.subset_span ⟨_,_,t,i,he.symm⟩

theorem first_mem (f : Fin n → F) (b : Fin m → B) (t : Fin n ⊕ Fin m) (i : I) :
    first f b t i ∈ grade F B I n m 1 := by
  have h := word_mem
    (fun j => (f j,if Sum.inl j = t then Finsupp.single i 1 else 0))
    (fun j => (b j,if Sum.inr j = t then Finsupp.single i 1 else 0))
  have ho : wordOrder
      (fun j => (f j,if Sum.inl j = t then Finsupp.single i 1 else 0))
      (fun j => (b j,if Sum.inr j = t then Finsupp.single i 1 else 0)) = 1 := by
    cases t <;> simp [wordOrder,order,apply_ite,Finsupp.weight_single]
  rw [ho] at h
  exact h

theorem grade_eq_span : grade F B I n m 1 =
    Submodule.span ℂ {p | ∃ (f : Fin n → F) (b : Fin m → B)
      (t : Fin n ⊕ Fin m) (i : I), first f b t i = p} := by
  apply le_antisymm grade_le_span
  apply Submodule.span_le.mpr
  rintro p ⟨f,b,t,i,rfl⟩
  exact first_mem f b t i

end
end Math.MixedFirstJetWords
