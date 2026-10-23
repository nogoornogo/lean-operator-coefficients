import Math.Algebra.Constructions.ColoredQuarticWords
import Math.Algebra.Constructions.ColoredDegreeFour

/-! Entire colored grade coverage, before equations or invariance. -/
namespace Math.ColoredQuarticSource
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial ColoredQuarticWords
variable {S : Type*}
abbrev J (S : Type*) := Index S (Fin 4)

theorem jet0 (j : J S) (hj : order j.2 = 0) :
    (X j : A S) = field j.1 := by
  rcases j with ⟨s,a⟩
  change order a = 0 at hj
  rw [ScalarDegreeTwo.order_zero hj]
  rfl

theorem jet1 (j : J S) (hj : order j.2 = 1) :
    ∃ i : Fin 4, (X j : A S) = j1 j.1 (E i) := by
  rcases j with ⟨s,a⟩
  change order a = 1 at hj
  obtain ⟨i,he⟩ := ScalarDegreeTwo.order_one hj
  refine ⟨i,?_⟩
  simp [j1,E,he,field,D,ScalarJetAlgebra.shift,add_comm]

theorem jet2 (j : J S) (hj : order j.2 = 2) :
    ∃ i k : Fin 4, (X j : A S) = j2 j.1 (E i) (E k) := by
  rcases j with ⟨s,a⟩
  change order a = 2 at hj
  obtain ⟨i,k,he⟩ := ScalarDegreeTwo.order_two hj
  refine ⟨i,k,?_⟩
  simp [j2,j1,E,he,field,D,ScalarJetAlgebra.shift,add_comm]

theorem jet3 (j : J S) (hj : order j.2 = 3) :
    ∃ i k l : Fin 4, (X j : A S) = j3 j.1 (E i) (E k) (E l) := by
  rcases j with ⟨s,a⟩
  change order a = 3 at hj
  obtain ⟨i,k,l,he⟩ := ScalarDegreeFour.order_three hj
  refine ⟨i,k,l,?_⟩
  simp [j3,j2,j1,E,he,field,D,ScalarJetAlgebra.shift,add_comm,add_left_comm]

theorem jet4 (j : J S) (hj : order j.2 = 4) :
    ∃ i k l m : Fin 4, (X j : A S) = j4 j.1 (E i) (E k) (E l) (E m) := by
  rcases j with ⟨s,a⟩
  change order a = 4 at hj
  obtain ⟨i,k,l,m,he⟩ := ScalarDegreeFour.order_four hj
  refine ⟨i,k,l,m,?_⟩
  simp [j4,j3,j2,j1,E,he,field,D,ScalarJetAlgebra.shift,add_comm,add_left_comm]

def words (S : Type*) : Set (A S) :=
  {p | ∃ a : Fin 4 → S, ∃ r : Fin 5, ∃ i j k l : Fin 4,
    p = word a r (E i) (E j) (E k) (E l)}
def wordSpan (S : Type*) : Submodule ℂ (A S) := Submodule.span ℂ (words S)
theorem word_mem (a : Fin 4 → S) (r : Fin 5) (i j k l : Fin 4) :
    word a r (E i) (E j) (E k) (E l) ∈ wordSpan S :=
  Submodule.subset_span ⟨a,r,i,j,k,l,rfl⟩

private theorem partitions0 (b c d : ℕ) (h : 0+b+c+d = 4) :
    ((((b = 0 ∧ c = 0 ∧ d = 4) ∨ ((b = 0 ∧ c = 1 ∧ d = 3) ∨ (b = 0 ∧ c = 2 ∧ d = 2))) ∨ (((b = 0 ∧ c = 3 ∧ d = 1) ∨ (b = 0 ∧ c = 4 ∧ d = 0)) ∨ ((b = 1 ∧ c = 0 ∧ d = 3) ∨ (b = 1 ∧ c = 1 ∧ d = 2)))) ∨ ((((b = 1 ∧ c = 2 ∧ d = 1) ∨ (b = 1 ∧ c = 3 ∧ d = 0)) ∨ ((b = 2 ∧ c = 0 ∧ d = 2) ∨ (b = 2 ∧ c = 1 ∧ d = 1))) ∨ (((b = 2 ∧ c = 2 ∧ d = 0) ∨ (b = 3 ∧ c = 0 ∧ d = 1)) ∨ ((b = 3 ∧ c = 1 ∧ d = 0) ∨ (b = 4 ∧ c = 0 ∧ d = 0))))) := by
  have hb : b ≤ 4 := by omega
  interval_cases b
  · have hc : c ≤ 4 := by omega
    interval_cases c
    · exact Or.inl (Or.inl (Or.inl (⟨rfl,rfl,by omega⟩)))
    · exact Or.inl (Or.inl (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩))))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (⟨rfl,rfl,by omega⟩))))
    · exact Or.inl (Or.inr (Or.inl (Or.inl (⟨rfl,rfl,by omega⟩))))
    · exact Or.inl (Or.inr (Or.inl (Or.inr (⟨rfl,rfl,by omega⟩))))
  · have hc : c ≤ 3 := by omega
    interval_cases c
    · exact Or.inl (Or.inr (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (⟨rfl,rfl,by omega⟩))))
    · exact Or.inr (Or.inl (Or.inl (Or.inl (⟨rfl,rfl,by omega⟩))))
    · exact Or.inr (Or.inl (Or.inl (Or.inr (⟨rfl,rfl,by omega⟩))))
  · have hc : c ≤ 2 := by omega
    interval_cases c
    · exact Or.inr (Or.inl (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (⟨rfl,rfl,by omega⟩))))
    · exact Or.inr (Or.inr (Or.inl (Or.inl (⟨rfl,rfl,by omega⟩))))
  · have hc : c ≤ 1 := by omega
    interval_cases c
    · exact Or.inr (Or.inr (Or.inl (Or.inr (⟨rfl,rfl,by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩))))
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl,rfl,by omega⟩))))

private theorem partitions1 (b c d : ℕ) (h : 1+b+c+d = 4) :
    ((((b = 0 ∧ c = 0 ∧ d = 3) ∨ (b = 0 ∧ c = 1 ∧ d = 2)) ∨ ((b = 0 ∧ c = 2 ∧ d = 1) ∨ ((b = 0 ∧ c = 3 ∧ d = 0) ∨ (b = 1 ∧ c = 0 ∧ d = 2)))) ∨ (((b = 1 ∧ c = 1 ∧ d = 1) ∨ (b = 1 ∧ c = 2 ∧ d = 0)) ∨ ((b = 2 ∧ c = 0 ∧ d = 1) ∨ ((b = 2 ∧ c = 1 ∧ d = 0) ∨ (b = 3 ∧ c = 0 ∧ d = 0))))) := by
  have hb : b ≤ 3 := by omega
  interval_cases b
  · have hc : c ≤ 3 := by omega
    interval_cases c
    · exact Or.inl (Or.inl (Or.inl (⟨rfl,rfl,by omega⟩)))
    · exact Or.inl (Or.inl (Or.inr (⟨rfl,rfl,by omega⟩)))
    · exact Or.inl (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩))))
  · have hc : c ≤ 2 := by omega
    interval_cases c
    · exact Or.inl (Or.inr (Or.inr (Or.inr (⟨rfl,rfl,by omega⟩))))
    · exact Or.inr (Or.inl (Or.inl (⟨rfl,rfl,by omega⟩)))
    · exact Or.inr (Or.inl (Or.inr (⟨rfl,rfl,by omega⟩)))
  · have hc : c ≤ 1 := by omega
    interval_cases c
    · exact Or.inr (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩))))
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl,rfl,by omega⟩))))

private theorem partitions2 (b c d : ℕ) (h : 2+b+c+d = 4) :
    (((b = 0 ∧ c = 0 ∧ d = 2) ∨ ((b = 0 ∧ c = 1 ∧ d = 1) ∨ (b = 0 ∧ c = 2 ∧ d = 0))) ∨ ((b = 1 ∧ c = 0 ∧ d = 1) ∨ ((b = 1 ∧ c = 1 ∧ d = 0) ∨ (b = 2 ∧ c = 0 ∧ d = 0)))) := by
  have hb : b ≤ 2 := by omega
  interval_cases b
  · have hc : c ≤ 2 := by omega
    interval_cases c
    · exact Or.inl (Or.inl (⟨rfl,rfl,by omega⟩))
    · exact Or.inl (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩)))
    · exact Or.inl (Or.inr (Or.inr (⟨rfl,rfl,by omega⟩)))
  · have hc : c ≤ 1 := by omega
    interval_cases c
    · exact Or.inr (Or.inl (⟨rfl,rfl,by omega⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨rfl,rfl,by omega⟩)))
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · exact Or.inr (Or.inr (Or.inr (⟨rfl,rfl,by omega⟩)))

private theorem partitions3 (b c d : ℕ) (h : 3+b+c+d = 4) :
    ((b = 0 ∧ c = 0 ∧ d = 1) ∨ ((b = 0 ∧ c = 1 ∧ d = 0) ∨ (b = 1 ∧ c = 0 ∧ d = 0))) := by
  have hb : b ≤ 1 := by omega
  interval_cases b
  · have hc : c ≤ 1 := by omega
    interval_cases c
    · exact Or.inl (⟨rfl,rfl,by omega⟩)
    · exact Or.inr (Or.inl (⟨rfl,rfl,by omega⟩))
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · exact Or.inr (Or.inr (⟨rfl,rfl,by omega⟩))

private theorem partitions4 (b c d : ℕ) (h : 4+b+c+d = 4) :
    (b = 0 ∧ c = 0 ∧ d = 0) := by
  have hb : b ≤ 0 := by omega
  interval_cases b
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · exact ⟨rfl,rfl,by omega⟩

theorem partitions (a b c d : ℕ) (h : a+b+c+d = 4) :
    ((((((a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 4) ∨ (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 3)) ∨ ((a = 0 ∧ b = 0 ∧ c = 2 ∧ d = 2) ∨ (a = 0 ∧ b = 0 ∧ c = 3 ∧ d = 1))) ∨ (((a = 0 ∧ b = 0 ∧ c = 4 ∧ d = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 3)) ∨ ((a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 2) ∨ (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 1)))) ∨ ((((a = 0 ∧ b = 1 ∧ c = 3 ∧ d = 0) ∨ (a = 0 ∧ b = 2 ∧ c = 0 ∧ d = 2)) ∨ ((a = 0 ∧ b = 2 ∧ c = 1 ∧ d = 1) ∨ (a = 0 ∧ b = 2 ∧ c = 2 ∧ d = 0))) ∨ (((a = 0 ∧ b = 3 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 3 ∧ c = 1 ∧ d = 0)) ∨ ((a = 0 ∧ b = 4 ∧ c = 0 ∧ d = 0) ∨ ((a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 3) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 2)))))) ∨ (((((a = 1 ∧ b = 0 ∧ c = 2 ∧ d = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 3 ∧ d = 0)) ∨ ((a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 2) ∨ (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1))) ∨ (((a = 1 ∧ b = 1 ∧ c = 2 ∧ d = 0) ∨ (a = 1 ∧ b = 2 ∧ c = 0 ∧ d = 1)) ∨ ((a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 0) ∨ ((a = 1 ∧ b = 3 ∧ c = 0 ∧ d = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 2))))) ∨ ((((a = 2 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨ (a = 2 ∧ b = 0 ∧ c = 2 ∧ d = 0)) ∨ ((a = 2 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 0))) ∨ (((a = 2 ∧ b = 2 ∧ c = 0 ∧ d = 0) ∨ (a = 3 ∧ b = 0 ∧ c = 0 ∧ d = 1)) ∨ ((a = 3 ∧ b = 0 ∧ c = 1 ∧ d = 0) ∨ ((a = 3 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∨ (a = 4 ∧ b = 0 ∧ c = 0 ∧ d = 0))))))) := by
  have ha : a ≤ 4 := by omega
  interval_cases a
  · have he := partitions0 b c d h
    rcases he with (((he | (he | he)) | ((he | he) | (he | he))) | (((he | he) | (he | he)) | ((he | he) | (he | he))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl,he⟩)))))
  · have he := partitions1 b c d h
    rcases he with (((he | he) | (he | (he | he))) | ((he | he) | (he | (he | he))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl,he⟩))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl,he⟩))))))
    · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl,he⟩))))))
  · have he := partitions2 b c d h
    rcases he with ((he | (he | he)) | (he | (he | he)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl,he⟩))))))
    · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (⟨rfl,he⟩)))))
  · have he := partitions3 b c d h
    rcases he with (he | (he | he))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl,he⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl,he⟩))))))
  · have he := partitions4 b c d h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl,he⟩))))))


private theorem allocation0 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 0) (hl : order l.2 = 0) (hm : order m.2 = 4) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  have ek := jet0 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,a_m1,a_m2,a_m3,em⟩ := jet4 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(field k.1)*(field l.1)*(j4 m.1 (E a_m0) (E a_m1) (E a_m2) (E a_m3)) = word ![j.1,k.1,l.1,m.1] 0 (E a_m0) (E a_m1) (E a_m2) (E a_m3) := by
    change (field j.1)*(field k.1)*(field l.1)*(j4 m.1 (E a_m0) (E a_m1) (E a_m2) (E a_m3)) = (field j.1)*(field k.1)*(field l.1)*(j4 m.1 (E a_m0) (E a_m1) (E a_m2) (E a_m3))
    ring
  rw [he]
  exact word_mem ![j.1,k.1,l.1,m.1] 0 a_m0 a_m1 a_m2 a_m3

private theorem allocation1 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 0) (hl : order l.2 = 1) (hm : order m.2 = 3) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  obtain ⟨a_m0,a_m1,a_m2,em⟩ := jet3 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(field k.1)*(j1 l.1 (E a_l0))*(j3 m.1 (E a_m0) (E a_m1) (E a_m2)) = word ![j.1,k.1,m.1,l.1] 1 (E a_m0) (E a_m1) (E a_m2) (E a_l0) := by
    change (field j.1)*(field k.1)*(j1 l.1 (E a_l0))*(j3 m.1 (E a_m0) (E a_m1) (E a_m2)) = (field j.1)*(field k.1)*(j3 m.1 (E a_m0) (E a_m1) (E a_m2))*(j1 l.1 (E a_l0))
    ring
  rw [he]
  exact word_mem ![j.1,k.1,m.1,l.1] 1 a_m0 a_m1 a_m2 a_l0

private theorem allocation2 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 0) (hl : order l.2 = 2) (hm : order m.2 = 2) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
  obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(field k.1)*(j2 l.1 (E a_l0) (E a_l1))*(j2 m.1 (E a_m0) (E a_m1)) = word ![j.1,k.1,l.1,m.1] 2 (E a_l0) (E a_l1) (E a_m0) (E a_m1) := by
    change (field j.1)*(field k.1)*(j2 l.1 (E a_l0) (E a_l1))*(j2 m.1 (E a_m0) (E a_m1)) = (field j.1)*(field k.1)*(j2 l.1 (E a_l0) (E a_l1))*(j2 m.1 (E a_m0) (E a_m1))
    ring
  rw [he]
  exact word_mem ![j.1,k.1,l.1,m.1] 2 a_l0 a_l1 a_m0 a_m1

private theorem allocation3 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 0) (hl : order l.2 = 3) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,a_l1,a_l2,el⟩ := jet3 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(field k.1)*(j3 l.1 (E a_l0) (E a_l1) (E a_l2))*(j1 m.1 (E a_m0)) = word ![j.1,k.1,l.1,m.1] 1 (E a_l0) (E a_l1) (E a_l2) (E a_m0) := by
    change (field j.1)*(field k.1)*(j3 l.1 (E a_l0) (E a_l1) (E a_l2))*(j1 m.1 (E a_m0)) = (field j.1)*(field k.1)*(j3 l.1 (E a_l0) (E a_l1) (E a_l2))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![j.1,k.1,l.1,m.1] 1 a_l0 a_l1 a_l2 a_m0

private theorem allocation4 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 0) (hl : order l.2 = 4) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,a_l1,a_l2,a_l3,el⟩ := jet4 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(field k.1)*(j4 l.1 (E a_l0) (E a_l1) (E a_l2) (E a_l3))*(field m.1) = word ![j.1,k.1,m.1,l.1] 0 (E a_l0) (E a_l1) (E a_l2) (E a_l3) := by
    change (field j.1)*(field k.1)*(j4 l.1 (E a_l0) (E a_l1) (E a_l2) (E a_l3))*(field m.1) = (field j.1)*(field k.1)*(field m.1)*(j4 l.1 (E a_l0) (E a_l1) (E a_l2) (E a_l3))
    ring
  rw [he]
  exact word_mem ![j.1,k.1,m.1,l.1] 0 a_l0 a_l1 a_l2 a_l3

private theorem allocation5 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 1) (hl : order l.2 = 0) (hm : order m.2 = 3) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,a_m1,a_m2,em⟩ := jet3 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j1 k.1 (E a_k0))*(field l.1)*(j3 m.1 (E a_m0) (E a_m1) (E a_m2)) = word ![j.1,l.1,m.1,k.1] 1 (E a_m0) (E a_m1) (E a_m2) (E a_k0) := by
    change (field j.1)*(j1 k.1 (E a_k0))*(field l.1)*(j3 m.1 (E a_m0) (E a_m1) (E a_m2)) = (field j.1)*(field l.1)*(j3 m.1 (E a_m0) (E a_m1) (E a_m2))*(j1 k.1 (E a_k0))
    ring
  rw [he]
  exact word_mem ![j.1,l.1,m.1,k.1] 1 a_m0 a_m1 a_m2 a_k0

private theorem allocation6 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 1) (hl : order l.2 = 1) (hm : order m.2 = 2) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j1 k.1 (E a_k0))*(j1 l.1 (E a_l0))*(j2 m.1 (E a_m0) (E a_m1)) = word ![j.1,m.1,k.1,l.1] 3 (E a_m0) (E a_m1) (E a_k0) (E a_l0) := by
    change (field j.1)*(j1 k.1 (E a_k0))*(j1 l.1 (E a_l0))*(j2 m.1 (E a_m0) (E a_m1)) = (field j.1)*(j2 m.1 (E a_m0) (E a_m1))*(j1 k.1 (E a_k0))*(j1 l.1 (E a_l0))
    ring
  rw [he]
  exact word_mem ![j.1,m.1,k.1,l.1] 3 a_m0 a_m1 a_k0 a_l0

private theorem allocation7 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 1) (hl : order l.2 = 2) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j1 k.1 (E a_k0))*(j2 l.1 (E a_l0) (E a_l1))*(j1 m.1 (E a_m0)) = word ![j.1,l.1,k.1,m.1] 3 (E a_l0) (E a_l1) (E a_k0) (E a_m0) := by
    change (field j.1)*(j1 k.1 (E a_k0))*(j2 l.1 (E a_l0) (E a_l1))*(j1 m.1 (E a_m0)) = (field j.1)*(j2 l.1 (E a_l0) (E a_l1))*(j1 k.1 (E a_k0))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![j.1,l.1,k.1,m.1] 3 a_l0 a_l1 a_k0 a_m0

private theorem allocation8 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 1) (hl : order l.2 = 3) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  obtain ⟨a_l0,a_l1,a_l2,el⟩ := jet3 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j1 k.1 (E a_k0))*(j3 l.1 (E a_l0) (E a_l1) (E a_l2))*(field m.1) = word ![j.1,m.1,l.1,k.1] 1 (E a_l0) (E a_l1) (E a_l2) (E a_k0) := by
    change (field j.1)*(j1 k.1 (E a_k0))*(j3 l.1 (E a_l0) (E a_l1) (E a_l2))*(field m.1) = (field j.1)*(field m.1)*(j3 l.1 (E a_l0) (E a_l1) (E a_l2))*(j1 k.1 (E a_k0))
    ring
  rw [he]
  exact word_mem ![j.1,m.1,l.1,k.1] 1 a_l0 a_l1 a_l2 a_k0

private theorem allocation9 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 2) (hl : order l.2 = 0) (hm : order m.2 = 2) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j2 k.1 (E a_k0) (E a_k1))*(field l.1)*(j2 m.1 (E a_m0) (E a_m1)) = word ![j.1,l.1,k.1,m.1] 2 (E a_k0) (E a_k1) (E a_m0) (E a_m1) := by
    change (field j.1)*(j2 k.1 (E a_k0) (E a_k1))*(field l.1)*(j2 m.1 (E a_m0) (E a_m1)) = (field j.1)*(field l.1)*(j2 k.1 (E a_k0) (E a_k1))*(j2 m.1 (E a_m0) (E a_m1))
    ring
  rw [he]
  exact word_mem ![j.1,l.1,k.1,m.1] 2 a_k0 a_k1 a_m0 a_m1

private theorem allocation10 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 2) (hl : order l.2 = 1) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j2 k.1 (E a_k0) (E a_k1))*(j1 l.1 (E a_l0))*(j1 m.1 (E a_m0)) = word ![j.1,k.1,l.1,m.1] 3 (E a_k0) (E a_k1) (E a_l0) (E a_m0) := by
    change (field j.1)*(j2 k.1 (E a_k0) (E a_k1))*(j1 l.1 (E a_l0))*(j1 m.1 (E a_m0)) = (field j.1)*(j2 k.1 (E a_k0) (E a_k1))*(j1 l.1 (E a_l0))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![j.1,k.1,l.1,m.1] 3 a_k0 a_k1 a_l0 a_m0

private theorem allocation11 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 2) (hl : order l.2 = 2) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
  obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j2 k.1 (E a_k0) (E a_k1))*(j2 l.1 (E a_l0) (E a_l1))*(field m.1) = word ![j.1,m.1,k.1,l.1] 2 (E a_k0) (E a_k1) (E a_l0) (E a_l1) := by
    change (field j.1)*(j2 k.1 (E a_k0) (E a_k1))*(j2 l.1 (E a_l0) (E a_l1))*(field m.1) = (field j.1)*(field m.1)*(j2 k.1 (E a_k0) (E a_k1))*(j2 l.1 (E a_l0) (E a_l1))
    ring
  rw [he]
  exact word_mem ![j.1,m.1,k.1,l.1] 2 a_k0 a_k1 a_l0 a_l1

private theorem allocation12 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 3) (hl : order l.2 = 0) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,a_k1,a_k2,ek⟩ := jet3 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j3 k.1 (E a_k0) (E a_k1) (E a_k2))*(field l.1)*(j1 m.1 (E a_m0)) = word ![j.1,l.1,k.1,m.1] 1 (E a_k0) (E a_k1) (E a_k2) (E a_m0) := by
    change (field j.1)*(j3 k.1 (E a_k0) (E a_k1) (E a_k2))*(field l.1)*(j1 m.1 (E a_m0)) = (field j.1)*(field l.1)*(j3 k.1 (E a_k0) (E a_k1) (E a_k2))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![j.1,l.1,k.1,m.1] 1 a_k0 a_k1 a_k2 a_m0

private theorem allocation13 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 3) (hl : order l.2 = 1) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,a_k1,a_k2,ek⟩ := jet3 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j3 k.1 (E a_k0) (E a_k1) (E a_k2))*(j1 l.1 (E a_l0))*(field m.1) = word ![j.1,m.1,k.1,l.1] 1 (E a_k0) (E a_k1) (E a_k2) (E a_l0) := by
    change (field j.1)*(j3 k.1 (E a_k0) (E a_k1) (E a_k2))*(j1 l.1 (E a_l0))*(field m.1) = (field j.1)*(field m.1)*(j3 k.1 (E a_k0) (E a_k1) (E a_k2))*(j1 l.1 (E a_l0))
    ring
  rw [he]
  exact word_mem ![j.1,m.1,k.1,l.1] 1 a_k0 a_k1 a_k2 a_l0

private theorem allocation14 (j k l m : J S)
    (hj : order j.2 = 0) (hk : order k.2 = 4) (hl : order l.2 = 0) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  have ej := jet0 j hj
  obtain ⟨a_k0,a_k1,a_k2,a_k3,ek⟩ := jet4 k hk
  have el := jet0 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (field j.1)*(j4 k.1 (E a_k0) (E a_k1) (E a_k2) (E a_k3))*(field l.1)*(field m.1) = word ![j.1,l.1,m.1,k.1] 0 (E a_k0) (E a_k1) (E a_k2) (E a_k3) := by
    change (field j.1)*(j4 k.1 (E a_k0) (E a_k1) (E a_k2) (E a_k3))*(field l.1)*(field m.1) = (field j.1)*(field l.1)*(field m.1)*(j4 k.1 (E a_k0) (E a_k1) (E a_k2) (E a_k3))
    ring
  rw [he]
  exact word_mem ![j.1,l.1,m.1,k.1] 0 a_k0 a_k1 a_k2 a_k3

private theorem allocation15 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 0) (hl : order l.2 = 0) (hm : order m.2 = 3) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  have ek := jet0 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,a_m1,a_m2,em⟩ := jet3 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(field k.1)*(field l.1)*(j3 m.1 (E a_m0) (E a_m1) (E a_m2)) = word ![k.1,l.1,m.1,j.1] 1 (E a_m0) (E a_m1) (E a_m2) (E a_j0) := by
    change (j1 j.1 (E a_j0))*(field k.1)*(field l.1)*(j3 m.1 (E a_m0) (E a_m1) (E a_m2)) = (field k.1)*(field l.1)*(j3 m.1 (E a_m0) (E a_m1) (E a_m2))*(j1 j.1 (E a_j0))
    ring
  rw [he]
  exact word_mem ![k.1,l.1,m.1,j.1] 1 a_m0 a_m1 a_m2 a_j0

private theorem allocation16 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 0) (hl : order l.2 = 1) (hm : order m.2 = 2) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(field k.1)*(j1 l.1 (E a_l0))*(j2 m.1 (E a_m0) (E a_m1)) = word ![k.1,m.1,j.1,l.1] 3 (E a_m0) (E a_m1) (E a_j0) (E a_l0) := by
    change (j1 j.1 (E a_j0))*(field k.1)*(j1 l.1 (E a_l0))*(j2 m.1 (E a_m0) (E a_m1)) = (field k.1)*(j2 m.1 (E a_m0) (E a_m1))*(j1 j.1 (E a_j0))*(j1 l.1 (E a_l0))
    ring
  rw [he]
  exact word_mem ![k.1,m.1,j.1,l.1] 3 a_m0 a_m1 a_j0 a_l0

private theorem allocation17 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 0) (hl : order l.2 = 2) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(field k.1)*(j2 l.1 (E a_l0) (E a_l1))*(j1 m.1 (E a_m0)) = word ![k.1,l.1,j.1,m.1] 3 (E a_l0) (E a_l1) (E a_j0) (E a_m0) := by
    change (j1 j.1 (E a_j0))*(field k.1)*(j2 l.1 (E a_l0) (E a_l1))*(j1 m.1 (E a_m0)) = (field k.1)*(j2 l.1 (E a_l0) (E a_l1))*(j1 j.1 (E a_j0))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![k.1,l.1,j.1,m.1] 3 a_l0 a_l1 a_j0 a_m0

private theorem allocation18 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 0) (hl : order l.2 = 3) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,a_l1,a_l2,el⟩ := jet3 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(field k.1)*(j3 l.1 (E a_l0) (E a_l1) (E a_l2))*(field m.1) = word ![k.1,m.1,l.1,j.1] 1 (E a_l0) (E a_l1) (E a_l2) (E a_j0) := by
    change (j1 j.1 (E a_j0))*(field k.1)*(j3 l.1 (E a_l0) (E a_l1) (E a_l2))*(field m.1) = (field k.1)*(field m.1)*(j3 l.1 (E a_l0) (E a_l1) (E a_l2))*(j1 j.1 (E a_j0))
    ring
  rw [he]
  exact word_mem ![k.1,m.1,l.1,j.1] 1 a_l0 a_l1 a_l2 a_j0

private theorem allocation19 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 1) (hl : order l.2 = 0) (hm : order m.2 = 2) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(j1 k.1 (E a_k0))*(field l.1)*(j2 m.1 (E a_m0) (E a_m1)) = word ![l.1,m.1,j.1,k.1] 3 (E a_m0) (E a_m1) (E a_j0) (E a_k0) := by
    change (j1 j.1 (E a_j0))*(j1 k.1 (E a_k0))*(field l.1)*(j2 m.1 (E a_m0) (E a_m1)) = (field l.1)*(j2 m.1 (E a_m0) (E a_m1))*(j1 j.1 (E a_j0))*(j1 k.1 (E a_k0))
    ring
  rw [he]
  exact word_mem ![l.1,m.1,j.1,k.1] 3 a_m0 a_m1 a_j0 a_k0

private theorem allocation20 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 1) (hl : order l.2 = 1) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(j1 k.1 (E a_k0))*(j1 l.1 (E a_l0))*(j1 m.1 (E a_m0)) = word ![j.1,k.1,l.1,m.1] 4 (E a_j0) (E a_k0) (E a_l0) (E a_m0) := by
    change (j1 j.1 (E a_j0))*(j1 k.1 (E a_k0))*(j1 l.1 (E a_l0))*(j1 m.1 (E a_m0)) = (j1 j.1 (E a_j0))*(j1 k.1 (E a_k0))*(j1 l.1 (E a_l0))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![j.1,k.1,l.1,m.1] 4 a_j0 a_k0 a_l0 a_m0

private theorem allocation21 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 1) (hl : order l.2 = 2) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(j1 k.1 (E a_k0))*(j2 l.1 (E a_l0) (E a_l1))*(field m.1) = word ![m.1,l.1,j.1,k.1] 3 (E a_l0) (E a_l1) (E a_j0) (E a_k0) := by
    change (j1 j.1 (E a_j0))*(j1 k.1 (E a_k0))*(j2 l.1 (E a_l0) (E a_l1))*(field m.1) = (field m.1)*(j2 l.1 (E a_l0) (E a_l1))*(j1 j.1 (E a_j0))*(j1 k.1 (E a_k0))
    ring
  rw [he]
  exact word_mem ![m.1,l.1,j.1,k.1] 3 a_l0 a_l1 a_j0 a_k0

private theorem allocation22 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 2) (hl : order l.2 = 0) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(j2 k.1 (E a_k0) (E a_k1))*(field l.1)*(j1 m.1 (E a_m0)) = word ![l.1,k.1,j.1,m.1] 3 (E a_k0) (E a_k1) (E a_j0) (E a_m0) := by
    change (j1 j.1 (E a_j0))*(j2 k.1 (E a_k0) (E a_k1))*(field l.1)*(j1 m.1 (E a_m0)) = (field l.1)*(j2 k.1 (E a_k0) (E a_k1))*(j1 j.1 (E a_j0))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![l.1,k.1,j.1,m.1] 3 a_k0 a_k1 a_j0 a_m0

private theorem allocation23 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 2) (hl : order l.2 = 1) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(j2 k.1 (E a_k0) (E a_k1))*(j1 l.1 (E a_l0))*(field m.1) = word ![m.1,k.1,j.1,l.1] 3 (E a_k0) (E a_k1) (E a_j0) (E a_l0) := by
    change (j1 j.1 (E a_j0))*(j2 k.1 (E a_k0) (E a_k1))*(j1 l.1 (E a_l0))*(field m.1) = (field m.1)*(j2 k.1 (E a_k0) (E a_k1))*(j1 j.1 (E a_j0))*(j1 l.1 (E a_l0))
    ring
  rw [he]
  exact word_mem ![m.1,k.1,j.1,l.1] 3 a_k0 a_k1 a_j0 a_l0

private theorem allocation24 (j k l m : J S)
    (hj : order j.2 = 1) (hk : order k.2 = 3) (hl : order l.2 = 0) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,ej⟩ := jet1 j hj
  obtain ⟨a_k0,a_k1,a_k2,ek⟩ := jet3 k hk
  have el := jet0 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j1 j.1 (E a_j0))*(j3 k.1 (E a_k0) (E a_k1) (E a_k2))*(field l.1)*(field m.1) = word ![l.1,m.1,k.1,j.1] 1 (E a_k0) (E a_k1) (E a_k2) (E a_j0) := by
    change (j1 j.1 (E a_j0))*(j3 k.1 (E a_k0) (E a_k1) (E a_k2))*(field l.1)*(field m.1) = (field l.1)*(field m.1)*(j3 k.1 (E a_k0) (E a_k1) (E a_k2))*(j1 j.1 (E a_j0))
    ring
  rw [he]
  exact word_mem ![l.1,m.1,k.1,j.1] 1 a_k0 a_k1 a_k2 a_j0

private theorem allocation25 (j k l m : J S)
    (hj : order j.2 = 2) (hk : order k.2 = 0) (hl : order l.2 = 0) (hm : order m.2 = 2) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
  have ek := jet0 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
  rw [ej,ek,el,em]
  have he : (j2 j.1 (E a_j0) (E a_j1))*(field k.1)*(field l.1)*(j2 m.1 (E a_m0) (E a_m1)) = word ![k.1,l.1,j.1,m.1] 2 (E a_j0) (E a_j1) (E a_m0) (E a_m1) := by
    change (j2 j.1 (E a_j0) (E a_j1))*(field k.1)*(field l.1)*(j2 m.1 (E a_m0) (E a_m1)) = (field k.1)*(field l.1)*(j2 j.1 (E a_j0) (E a_j1))*(j2 m.1 (E a_m0) (E a_m1))
    ring
  rw [he]
  exact word_mem ![k.1,l.1,j.1,m.1] 2 a_j0 a_j1 a_m0 a_m1

private theorem allocation26 (j k l m : J S)
    (hj : order j.2 = 2) (hk : order k.2 = 0) (hl : order l.2 = 1) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (j2 j.1 (E a_j0) (E a_j1))*(field k.1)*(j1 l.1 (E a_l0))*(j1 m.1 (E a_m0)) = word ![k.1,j.1,l.1,m.1] 3 (E a_j0) (E a_j1) (E a_l0) (E a_m0) := by
    change (j2 j.1 (E a_j0) (E a_j1))*(field k.1)*(j1 l.1 (E a_l0))*(j1 m.1 (E a_m0)) = (field k.1)*(j2 j.1 (E a_j0) (E a_j1))*(j1 l.1 (E a_l0))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![k.1,j.1,l.1,m.1] 3 a_j0 a_j1 a_l0 a_m0

private theorem allocation27 (j k l m : J S)
    (hj : order j.2 = 2) (hk : order k.2 = 0) (hl : order l.2 = 2) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j2 j.1 (E a_j0) (E a_j1))*(field k.1)*(j2 l.1 (E a_l0) (E a_l1))*(field m.1) = word ![k.1,m.1,j.1,l.1] 2 (E a_j0) (E a_j1) (E a_l0) (E a_l1) := by
    change (j2 j.1 (E a_j0) (E a_j1))*(field k.1)*(j2 l.1 (E a_l0) (E a_l1))*(field m.1) = (field k.1)*(field m.1)*(j2 j.1 (E a_j0) (E a_j1))*(j2 l.1 (E a_l0) (E a_l1))
    ring
  rw [he]
  exact word_mem ![k.1,m.1,j.1,l.1] 2 a_j0 a_j1 a_l0 a_l1

private theorem allocation28 (j k l m : J S)
    (hj : order j.2 = 2) (hk : order k.2 = 1) (hl : order l.2 = 0) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (j2 j.1 (E a_j0) (E a_j1))*(j1 k.1 (E a_k0))*(field l.1)*(j1 m.1 (E a_m0)) = word ![l.1,j.1,k.1,m.1] 3 (E a_j0) (E a_j1) (E a_k0) (E a_m0) := by
    change (j2 j.1 (E a_j0) (E a_j1))*(j1 k.1 (E a_k0))*(field l.1)*(j1 m.1 (E a_m0)) = (field l.1)*(j2 j.1 (E a_j0) (E a_j1))*(j1 k.1 (E a_k0))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![l.1,j.1,k.1,m.1] 3 a_j0 a_j1 a_k0 a_m0

private theorem allocation29 (j k l m : J S)
    (hj : order j.2 = 2) (hk : order k.2 = 1) (hl : order l.2 = 1) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j2 j.1 (E a_j0) (E a_j1))*(j1 k.1 (E a_k0))*(j1 l.1 (E a_l0))*(field m.1) = word ![m.1,j.1,k.1,l.1] 3 (E a_j0) (E a_j1) (E a_k0) (E a_l0) := by
    change (j2 j.1 (E a_j0) (E a_j1))*(j1 k.1 (E a_k0))*(j1 l.1 (E a_l0))*(field m.1) = (field m.1)*(j2 j.1 (E a_j0) (E a_j1))*(j1 k.1 (E a_k0))*(j1 l.1 (E a_l0))
    ring
  rw [he]
  exact word_mem ![m.1,j.1,k.1,l.1] 3 a_j0 a_j1 a_k0 a_l0

private theorem allocation30 (j k l m : J S)
    (hj : order j.2 = 2) (hk : order k.2 = 2) (hl : order l.2 = 0) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
  obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
  have el := jet0 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j2 j.1 (E a_j0) (E a_j1))*(j2 k.1 (E a_k0) (E a_k1))*(field l.1)*(field m.1) = word ![l.1,m.1,j.1,k.1] 2 (E a_j0) (E a_j1) (E a_k0) (E a_k1) := by
    change (j2 j.1 (E a_j0) (E a_j1))*(j2 k.1 (E a_k0) (E a_k1))*(field l.1)*(field m.1) = (field l.1)*(field m.1)*(j2 j.1 (E a_j0) (E a_j1))*(j2 k.1 (E a_k0) (E a_k1))
    ring
  rw [he]
  exact word_mem ![l.1,m.1,j.1,k.1] 2 a_j0 a_j1 a_k0 a_k1

private theorem allocation31 (j k l m : J S)
    (hj : order j.2 = 3) (hk : order k.2 = 0) (hl : order l.2 = 0) (hm : order m.2 = 1) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,a_j2,ej⟩ := jet3 j hj
  have ek := jet0 k hk
  have el := jet0 l hl
  obtain ⟨a_m0,em⟩ := jet1 m hm
  rw [ej,ek,el,em]
  have he : (j3 j.1 (E a_j0) (E a_j1) (E a_j2))*(field k.1)*(field l.1)*(j1 m.1 (E a_m0)) = word ![k.1,l.1,j.1,m.1] 1 (E a_j0) (E a_j1) (E a_j2) (E a_m0) := by
    change (j3 j.1 (E a_j0) (E a_j1) (E a_j2))*(field k.1)*(field l.1)*(j1 m.1 (E a_m0)) = (field k.1)*(field l.1)*(j3 j.1 (E a_j0) (E a_j1) (E a_j2))*(j1 m.1 (E a_m0))
    ring
  rw [he]
  exact word_mem ![k.1,l.1,j.1,m.1] 1 a_j0 a_j1 a_j2 a_m0

private theorem allocation32 (j k l m : J S)
    (hj : order j.2 = 3) (hk : order k.2 = 0) (hl : order l.2 = 1) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,a_j2,ej⟩ := jet3 j hj
  have ek := jet0 k hk
  obtain ⟨a_l0,el⟩ := jet1 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j3 j.1 (E a_j0) (E a_j1) (E a_j2))*(field k.1)*(j1 l.1 (E a_l0))*(field m.1) = word ![k.1,m.1,j.1,l.1] 1 (E a_j0) (E a_j1) (E a_j2) (E a_l0) := by
    change (j3 j.1 (E a_j0) (E a_j1) (E a_j2))*(field k.1)*(j1 l.1 (E a_l0))*(field m.1) = (field k.1)*(field m.1)*(j3 j.1 (E a_j0) (E a_j1) (E a_j2))*(j1 l.1 (E a_l0))
    ring
  rw [he]
  exact word_mem ![k.1,m.1,j.1,l.1] 1 a_j0 a_j1 a_j2 a_l0

private theorem allocation33 (j k l m : J S)
    (hj : order j.2 = 3) (hk : order k.2 = 1) (hl : order l.2 = 0) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,a_j2,ej⟩ := jet3 j hj
  obtain ⟨a_k0,ek⟩ := jet1 k hk
  have el := jet0 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j3 j.1 (E a_j0) (E a_j1) (E a_j2))*(j1 k.1 (E a_k0))*(field l.1)*(field m.1) = word ![l.1,m.1,j.1,k.1] 1 (E a_j0) (E a_j1) (E a_j2) (E a_k0) := by
    change (j3 j.1 (E a_j0) (E a_j1) (E a_j2))*(j1 k.1 (E a_k0))*(field l.1)*(field m.1) = (field l.1)*(field m.1)*(j3 j.1 (E a_j0) (E a_j1) (E a_j2))*(j1 k.1 (E a_k0))
    ring
  rw [he]
  exact word_mem ![l.1,m.1,j.1,k.1] 1 a_j0 a_j1 a_j2 a_k0

private theorem allocation34 (j k l m : J S)
    (hj : order j.2 = 4) (hk : order k.2 = 0) (hl : order l.2 = 0) (hm : order m.2 = 0) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  obtain ⟨a_j0,a_j1,a_j2,a_j3,ej⟩ := jet4 j hj
  have ek := jet0 k hk
  have el := jet0 l hl
  have em := jet0 m hm
  rw [ej,ek,el,em]
  have he : (j4 j.1 (E a_j0) (E a_j1) (E a_j2) (E a_j3))*(field k.1)*(field l.1)*(field m.1) = word ![k.1,l.1,m.1,j.1] 0 (E a_j0) (E a_j1) (E a_j2) (E a_j3) := by
    change (j4 j.1 (E a_j0) (E a_j1) (E a_j2) (E a_j3))*(field k.1)*(field l.1)*(field m.1) = (field k.1)*(field l.1)*(field m.1)*(j4 j.1 (E a_j0) (E a_j1) (E a_j2) (E a_j3))
    ring
  rw [he]
  exact word_mem ![k.1,l.1,m.1,j.1] 0 a_j0 a_j1 a_j2 a_j3

theorem product_mem (j k l m : J S)
    (hd : order j.2+order k.2+order l.2+order m.2 = 4) :
    (X j*X k*X l*X m : A S) ∈ wordSpan S := by
  rcases partitions _ _ _ _ hd with (((((h | h) | (h | h)) | ((h | h) | (h | h))) | (((h | h) | (h | h)) | ((h | h) | (h | (h | h))))) | ((((h | h) | (h | h)) | ((h | h) | (h | (h | h)))) | (((h | h) | (h | h)) | ((h | h) | (h | (h | h))))))
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation0 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation1 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation2 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation3 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation4 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation5 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation6 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation7 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation8 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation9 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation10 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation11 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation12 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation13 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation14 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation15 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation16 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation17 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation18 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation19 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation20 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation21 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation22 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation23 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation24 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation25 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation26 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation27 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation28 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation29 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation30 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation31 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation32 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation33 j k l m hj hk hl hm
  · obtain ⟨hj,hk,hl,hm⟩ := h
    exact allocation34 j k l m hj hk hl hm

theorem grade_eq_span : V S = wordSpan S := by
  apply le_antisymm
  · intro p hp
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro a ha
    have hw := hp (MvPolynomial.mem_support_iff.mp ha)
    obtain ⟨j,k,l,m,he,hd⟩ := ColoredDegreeFour.monomial_four hw
    have hc : (monomial a (p.coeff a) : A S) = p.coeff a • monomial a 1 := by
      simp [smul_monomial]
    rw [hc,he]
    exact (wordSpan S).smul_mem _ (product_mem j k l m hd)
  · apply Submodule.span_le.mpr
    rintro p ⟨a,r,i,j,k,l,rfl⟩
    exact word_grade a r (E i) (E j) (E k) (E l)

end
end Math.ColoredQuarticSource
