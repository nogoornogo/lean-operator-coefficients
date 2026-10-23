import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourTensors

/-! Complete source coverage by the five derivative partitions. -/
namespace Physics.ScalarQuarticFourSource
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM ScalarQuarticFourTensors LorentzFiniteControls
abbrev J := ScalarJetAlgebra.Index Unit (Fin 4)

theorem jet0 (j : J) (hj : ScalarJetAlgebra.order j.2 = 0) : (X j : OffShell) = field := by
  rcases j with ⟨⟨⟩,a⟩
  change ScalarJetAlgebra.order a = 0 at hj
  rw [ScalarDegreeTwo.order_zero hj]
  rfl

theorem jet1 (j : J) (hj : ScalarJetAlgebra.order j.2 = 1) :
    ∃ i : Fin 4, (X j : OffShell) = j1 (E i) := by
  rcases j with ⟨⟨⟩,a⟩
  change ScalarJetAlgebra.order a = 1 at hj
  obtain ⟨i,hi⟩ := ScalarDegreeTwo.order_one hj
  refine ⟨i,?_⟩
  simp [j1,E,hi,field,MasslessScalarEOM.field,D,ScalarJetAlgebra.shift]

theorem jet2 (j : J) (hj : ScalarJetAlgebra.order j.2 = 2) :
    ∃ i k : Fin 4, (X j : OffShell) = j2 (E i) (E k) := by
  rcases j with ⟨⟨⟩,a⟩
  change ScalarJetAlgebra.order a = 2 at hj
  obtain ⟨i,k,hik⟩ := ScalarDegreeTwo.order_two hj
  refine ⟨i,k,?_⟩
  simp [j2,j1,E,hik,field,MasslessScalarEOM.field,D,ScalarJetAlgebra.shift,add_comm]

theorem jet3 (j : J) (hj : ScalarJetAlgebra.order j.2 = 3) :
    ∃ i k l : Fin 4, (X j : OffShell) = j3 (E i) (E k) (E l) := by
  rcases j with ⟨⟨⟩,a⟩
  change ScalarJetAlgebra.order a = 3 at hj
  obtain ⟨i,k,l,hikl⟩ := ScalarDegreeFour.order_three hj
  refine ⟨i,k,l,?_⟩
  simp [j3,j2,j1,E,hikl,field,MasslessScalarEOM.field,D,ScalarJetAlgebra.shift,add_comm,add_left_comm]

theorem jet4 (j : J) (hj : ScalarJetAlgebra.order j.2 = 4) :
    ∃ i k l m : Fin 4, (X j : OffShell) = j4 (E i) (E k) (E l) (E m) := by
  rcases j with ⟨⟨⟩,a⟩
  change ScalarJetAlgebra.order a = 4 at hj
  obtain ⟨i,k,l,m,hiklm⟩ := ScalarDegreeFour.order_four hj
  refine ⟨i,k,l,m,?_⟩
  simp [j4,j3,j2,j1,E,hiklm,field,MasslessScalarEOM.field,D,ScalarJetAlgebra.shift,add_comm,add_left_comm]

def words : Set OffShell := {p | ∃ r : Fin 5, ∃ i j k l : Fin 4, p = word r (E i) (E j) (E k) (E l)}
def wordSpan : Submodule ℂ OffShell := Submodule.span ℂ words
theorem word_mem (r : Fin 5) (i j k l : Fin 4) : word r (E i) (E j) (E k) (E l) ∈ wordSpan :=
  Submodule.subset_span ⟨r,i,j,k,l,rfl⟩

/- Generated source coverage follows. -/

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

theorem product_mem (j k l m : J)
    (hd : ScalarJetAlgebra.order j.2+ScalarJetAlgebra.order k.2+
      ScalarJetAlgebra.order l.2+ScalarJetAlgebra.order m.2 = 4) :
    (X j*X k*X l*X m : OffShell) ∈ wordSpan := by
  rcases partitions _ _ _ _ hd with (((((h | h) | (h | h)) | ((h | h) | (h | h))) | (((h | h) | (h | h)) | ((h | h) | (h | (h | h))))) | ((((h | h) | (h | h)) | ((h | h) | (h | (h | h)))) | (((h | h) | (h | h)) | ((h | h) | (h | (h | h))))))
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    have ek := jet0 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,a_m1,a_m2,a_m3,em⟩ := jet4 m hm
    rw [ej,ek,el,em]
    have he : (field)*(field)*(field)*(j4 (E a_m0) (E a_m1) (E a_m2) (E a_m3)) = word 0 (E a_m0) (E a_m1) (E a_m2) (E a_m3) := by
      change (field)*(field)*(field)*(j4 (E a_m0) (E a_m1) (E a_m2) (E a_m3)) = field^3*(j4 (E a_m0) (E a_m1) (E a_m2) (E a_m3))
      ring
    rw [he]
    exact word_mem 0 a_m0 a_m1 a_m2 a_m3
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    obtain ⟨a_m0,a_m1,a_m2,em⟩ := jet3 m hm
    rw [ej,ek,el,em]
    have he : (field)*(field)*(j1 (E a_l0))*(j3 (E a_m0) (E a_m1) (E a_m2)) = word 1 (E a_m0) (E a_m1) (E a_m2) (E a_l0) := by
      change (field)*(field)*(j1 (E a_l0))*(j3 (E a_m0) (E a_m1) (E a_m2)) = field^2*(j3 (E a_m0) (E a_m1) (E a_m2))*(j1 (E a_l0))
      ring
    rw [he]
    exact word_mem 1 a_m0 a_m1 a_m2 a_l0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
    obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
    rw [ej,ek,el,em]
    have he : (field)*(field)*(j2 (E a_l0) (E a_l1))*(j2 (E a_m0) (E a_m1)) = word 2 (E a_l0) (E a_l1) (E a_m0) (E a_m1) := by
      change (field)*(field)*(j2 (E a_l0) (E a_l1))*(j2 (E a_m0) (E a_m1)) = field^2*(j2 (E a_l0) (E a_l1))*(j2 (E a_m0) (E a_m1))
      ring
    rw [he]
    exact word_mem 2 a_l0 a_l1 a_m0 a_m1
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,a_l1,a_l2,el⟩ := jet3 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (field)*(field)*(j3 (E a_l0) (E a_l1) (E a_l2))*(j1 (E a_m0)) = word 1 (E a_l0) (E a_l1) (E a_l2) (E a_m0) := by
      change (field)*(field)*(j3 (E a_l0) (E a_l1) (E a_l2))*(j1 (E a_m0)) = field^2*(j3 (E a_l0) (E a_l1) (E a_l2))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 1 a_l0 a_l1 a_l2 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,a_l1,a_l2,a_l3,el⟩ := jet4 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (field)*(field)*(j4 (E a_l0) (E a_l1) (E a_l2) (E a_l3))*(field) = word 0 (E a_l0) (E a_l1) (E a_l2) (E a_l3) := by
      change (field)*(field)*(j4 (E a_l0) (E a_l1) (E a_l2) (E a_l3))*(field) = field^3*(j4 (E a_l0) (E a_l1) (E a_l2) (E a_l3))
      ring
    rw [he]
    exact word_mem 0 a_l0 a_l1 a_l2 a_l3
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,a_m1,a_m2,em⟩ := jet3 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j1 (E a_k0))*(field)*(j3 (E a_m0) (E a_m1) (E a_m2)) = word 1 (E a_m0) (E a_m1) (E a_m2) (E a_k0) := by
      change (field)*(j1 (E a_k0))*(field)*(j3 (E a_m0) (E a_m1) (E a_m2)) = field^2*(j3 (E a_m0) (E a_m1) (E a_m2))*(j1 (E a_k0))
      ring
    rw [he]
    exact word_mem 1 a_m0 a_m1 a_m2 a_k0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j1 (E a_k0))*(j1 (E a_l0))*(j2 (E a_m0) (E a_m1)) = word 3 (E a_m0) (E a_m1) (E a_k0) (E a_l0) := by
      change (field)*(j1 (E a_k0))*(j1 (E a_l0))*(j2 (E a_m0) (E a_m1)) = field*(j2 (E a_m0) (E a_m1))*(j1 (E a_k0))*(j1 (E a_l0))
      ring
    rw [he]
    exact word_mem 3 a_m0 a_m1 a_k0 a_l0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j1 (E a_k0))*(j2 (E a_l0) (E a_l1))*(j1 (E a_m0)) = word 3 (E a_l0) (E a_l1) (E a_k0) (E a_m0) := by
      change (field)*(j1 (E a_k0))*(j2 (E a_l0) (E a_l1))*(j1 (E a_m0)) = field*(j2 (E a_l0) (E a_l1))*(j1 (E a_k0))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 3 a_l0 a_l1 a_k0 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    obtain ⟨a_l0,a_l1,a_l2,el⟩ := jet3 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j1 (E a_k0))*(j3 (E a_l0) (E a_l1) (E a_l2))*(field) = word 1 (E a_l0) (E a_l1) (E a_l2) (E a_k0) := by
      change (field)*(j1 (E a_k0))*(j3 (E a_l0) (E a_l1) (E a_l2))*(field) = field^2*(j3 (E a_l0) (E a_l1) (E a_l2))*(j1 (E a_k0))
      ring
    rw [he]
    exact word_mem 1 a_l0 a_l1 a_l2 a_k0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j2 (E a_k0) (E a_k1))*(field)*(j2 (E a_m0) (E a_m1)) = word 2 (E a_k0) (E a_k1) (E a_m0) (E a_m1) := by
      change (field)*(j2 (E a_k0) (E a_k1))*(field)*(j2 (E a_m0) (E a_m1)) = field^2*(j2 (E a_k0) (E a_k1))*(j2 (E a_m0) (E a_m1))
      ring
    rw [he]
    exact word_mem 2 a_k0 a_k1 a_m0 a_m1
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j2 (E a_k0) (E a_k1))*(j1 (E a_l0))*(j1 (E a_m0)) = word 3 (E a_k0) (E a_k1) (E a_l0) (E a_m0) := by
      change (field)*(j2 (E a_k0) (E a_k1))*(j1 (E a_l0))*(j1 (E a_m0)) = field*(j2 (E a_k0) (E a_k1))*(j1 (E a_l0))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 3 a_k0 a_k1 a_l0 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
    obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j2 (E a_k0) (E a_k1))*(j2 (E a_l0) (E a_l1))*(field) = word 2 (E a_k0) (E a_k1) (E a_l0) (E a_l1) := by
      change (field)*(j2 (E a_k0) (E a_k1))*(j2 (E a_l0) (E a_l1))*(field) = field^2*(j2 (E a_k0) (E a_k1))*(j2 (E a_l0) (E a_l1))
      ring
    rw [he]
    exact word_mem 2 a_k0 a_k1 a_l0 a_l1
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,a_k1,a_k2,ek⟩ := jet3 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j3 (E a_k0) (E a_k1) (E a_k2))*(field)*(j1 (E a_m0)) = word 1 (E a_k0) (E a_k1) (E a_k2) (E a_m0) := by
      change (field)*(j3 (E a_k0) (E a_k1) (E a_k2))*(field)*(j1 (E a_m0)) = field^2*(j3 (E a_k0) (E a_k1) (E a_k2))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 1 a_k0 a_k1 a_k2 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,a_k1,a_k2,ek⟩ := jet3 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j3 (E a_k0) (E a_k1) (E a_k2))*(j1 (E a_l0))*(field) = word 1 (E a_k0) (E a_k1) (E a_k2) (E a_l0) := by
      change (field)*(j3 (E a_k0) (E a_k1) (E a_k2))*(j1 (E a_l0))*(field) = field^2*(j3 (E a_k0) (E a_k1) (E a_k2))*(j1 (E a_l0))
      ring
    rw [he]
    exact word_mem 1 a_k0 a_k1 a_k2 a_l0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    have ej := jet0 j hj
    obtain ⟨a_k0,a_k1,a_k2,a_k3,ek⟩ := jet4 k hk
    have el := jet0 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (field)*(j4 (E a_k0) (E a_k1) (E a_k2) (E a_k3))*(field)*(field) = word 0 (E a_k0) (E a_k1) (E a_k2) (E a_k3) := by
      change (field)*(j4 (E a_k0) (E a_k1) (E a_k2) (E a_k3))*(field)*(field) = field^3*(j4 (E a_k0) (E a_k1) (E a_k2) (E a_k3))
      ring
    rw [he]
    exact word_mem 0 a_k0 a_k1 a_k2 a_k3
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    have ek := jet0 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,a_m1,a_m2,em⟩ := jet3 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(field)*(field)*(j3 (E a_m0) (E a_m1) (E a_m2)) = word 1 (E a_m0) (E a_m1) (E a_m2) (E a_j0) := by
      change (j1 (E a_j0))*(field)*(field)*(j3 (E a_m0) (E a_m1) (E a_m2)) = field^2*(j3 (E a_m0) (E a_m1) (E a_m2))*(j1 (E a_j0))
      ring
    rw [he]
    exact word_mem 1 a_m0 a_m1 a_m2 a_j0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(field)*(j1 (E a_l0))*(j2 (E a_m0) (E a_m1)) = word 3 (E a_m0) (E a_m1) (E a_j0) (E a_l0) := by
      change (j1 (E a_j0))*(field)*(j1 (E a_l0))*(j2 (E a_m0) (E a_m1)) = field*(j2 (E a_m0) (E a_m1))*(j1 (E a_j0))*(j1 (E a_l0))
      ring
    rw [he]
    exact word_mem 3 a_m0 a_m1 a_j0 a_l0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(field)*(j2 (E a_l0) (E a_l1))*(j1 (E a_m0)) = word 3 (E a_l0) (E a_l1) (E a_j0) (E a_m0) := by
      change (j1 (E a_j0))*(field)*(j2 (E a_l0) (E a_l1))*(j1 (E a_m0)) = field*(j2 (E a_l0) (E a_l1))*(j1 (E a_j0))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 3 a_l0 a_l1 a_j0 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,a_l1,a_l2,el⟩ := jet3 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(field)*(j3 (E a_l0) (E a_l1) (E a_l2))*(field) = word 1 (E a_l0) (E a_l1) (E a_l2) (E a_j0) := by
      change (j1 (E a_j0))*(field)*(j3 (E a_l0) (E a_l1) (E a_l2))*(field) = field^2*(j3 (E a_l0) (E a_l1) (E a_l2))*(j1 (E a_j0))
      ring
    rw [he]
    exact word_mem 1 a_l0 a_l1 a_l2 a_j0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(j1 (E a_k0))*(field)*(j2 (E a_m0) (E a_m1)) = word 3 (E a_m0) (E a_m1) (E a_j0) (E a_k0) := by
      change (j1 (E a_j0))*(j1 (E a_k0))*(field)*(j2 (E a_m0) (E a_m1)) = field*(j2 (E a_m0) (E a_m1))*(j1 (E a_j0))*(j1 (E a_k0))
      ring
    rw [he]
    exact word_mem 3 a_m0 a_m1 a_j0 a_k0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(j1 (E a_k0))*(j1 (E a_l0))*(j1 (E a_m0)) = word 4 (E a_j0) (E a_k0) (E a_l0) (E a_m0) := by
      change (j1 (E a_j0))*(j1 (E a_k0))*(j1 (E a_l0))*(j1 (E a_m0)) = (j1 (E a_j0))*(j1 (E a_k0))*(j1 (E a_l0))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 4 a_j0 a_k0 a_l0 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(j1 (E a_k0))*(j2 (E a_l0) (E a_l1))*(field) = word 3 (E a_l0) (E a_l1) (E a_j0) (E a_k0) := by
      change (j1 (E a_j0))*(j1 (E a_k0))*(j2 (E a_l0) (E a_l1))*(field) = field*(j2 (E a_l0) (E a_l1))*(j1 (E a_j0))*(j1 (E a_k0))
      ring
    rw [he]
    exact word_mem 3 a_l0 a_l1 a_j0 a_k0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(j2 (E a_k0) (E a_k1))*(field)*(j1 (E a_m0)) = word 3 (E a_k0) (E a_k1) (E a_j0) (E a_m0) := by
      change (j1 (E a_j0))*(j2 (E a_k0) (E a_k1))*(field)*(j1 (E a_m0)) = field*(j2 (E a_k0) (E a_k1))*(j1 (E a_j0))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 3 a_k0 a_k1 a_j0 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(j2 (E a_k0) (E a_k1))*(j1 (E a_l0))*(field) = word 3 (E a_k0) (E a_k1) (E a_j0) (E a_l0) := by
      change (j1 (E a_j0))*(j2 (E a_k0) (E a_k1))*(j1 (E a_l0))*(field) = field*(j2 (E a_k0) (E a_k1))*(j1 (E a_j0))*(j1 (E a_l0))
      ring
    rw [he]
    exact word_mem 3 a_k0 a_k1 a_j0 a_l0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,ej⟩ := jet1 j hj
    obtain ⟨a_k0,a_k1,a_k2,ek⟩ := jet3 k hk
    have el := jet0 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j1 (E a_j0))*(j3 (E a_k0) (E a_k1) (E a_k2))*(field)*(field) = word 1 (E a_k0) (E a_k1) (E a_k2) (E a_j0) := by
      change (j1 (E a_j0))*(j3 (E a_k0) (E a_k1) (E a_k2))*(field)*(field) = field^2*(j3 (E a_k0) (E a_k1) (E a_k2))*(j1 (E a_j0))
      ring
    rw [he]
    exact word_mem 1 a_k0 a_k1 a_k2 a_j0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
    have ek := jet0 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,a_m1,em⟩ := jet2 m hm
    rw [ej,ek,el,em]
    have he : (j2 (E a_j0) (E a_j1))*(field)*(field)*(j2 (E a_m0) (E a_m1)) = word 2 (E a_j0) (E a_j1) (E a_m0) (E a_m1) := by
      change (j2 (E a_j0) (E a_j1))*(field)*(field)*(j2 (E a_m0) (E a_m1)) = field^2*(j2 (E a_j0) (E a_j1))*(j2 (E a_m0) (E a_m1))
      ring
    rw [he]
    exact word_mem 2 a_j0 a_j1 a_m0 a_m1
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (j2 (E a_j0) (E a_j1))*(field)*(j1 (E a_l0))*(j1 (E a_m0)) = word 3 (E a_j0) (E a_j1) (E a_l0) (E a_m0) := by
      change (j2 (E a_j0) (E a_j1))*(field)*(j1 (E a_l0))*(j1 (E a_m0)) = field*(j2 (E a_j0) (E a_j1))*(j1 (E a_l0))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 3 a_j0 a_j1 a_l0 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,a_l1,el⟩ := jet2 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j2 (E a_j0) (E a_j1))*(field)*(j2 (E a_l0) (E a_l1))*(field) = word 2 (E a_j0) (E a_j1) (E a_l0) (E a_l1) := by
      change (j2 (E a_j0) (E a_j1))*(field)*(j2 (E a_l0) (E a_l1))*(field) = field^2*(j2 (E a_j0) (E a_j1))*(j2 (E a_l0) (E a_l1))
      ring
    rw [he]
    exact word_mem 2 a_j0 a_j1 a_l0 a_l1
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (j2 (E a_j0) (E a_j1))*(j1 (E a_k0))*(field)*(j1 (E a_m0)) = word 3 (E a_j0) (E a_j1) (E a_k0) (E a_m0) := by
      change (j2 (E a_j0) (E a_j1))*(j1 (E a_k0))*(field)*(j1 (E a_m0)) = field*(j2 (E a_j0) (E a_j1))*(j1 (E a_k0))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 3 a_j0 a_j1 a_k0 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j2 (E a_j0) (E a_j1))*(j1 (E a_k0))*(j1 (E a_l0))*(field) = word 3 (E a_j0) (E a_j1) (E a_k0) (E a_l0) := by
      change (j2 (E a_j0) (E a_j1))*(j1 (E a_k0))*(j1 (E a_l0))*(field) = field*(j2 (E a_j0) (E a_j1))*(j1 (E a_k0))*(j1 (E a_l0))
      ring
    rw [he]
    exact word_mem 3 a_j0 a_j1 a_k0 a_l0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,ej⟩ := jet2 j hj
    obtain ⟨a_k0,a_k1,ek⟩ := jet2 k hk
    have el := jet0 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j2 (E a_j0) (E a_j1))*(j2 (E a_k0) (E a_k1))*(field)*(field) = word 2 (E a_j0) (E a_j1) (E a_k0) (E a_k1) := by
      change (j2 (E a_j0) (E a_j1))*(j2 (E a_k0) (E a_k1))*(field)*(field) = field^2*(j2 (E a_j0) (E a_j1))*(j2 (E a_k0) (E a_k1))
      ring
    rw [he]
    exact word_mem 2 a_j0 a_j1 a_k0 a_k1
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,a_j2,ej⟩ := jet3 j hj
    have ek := jet0 k hk
    have el := jet0 l hl
    obtain ⟨a_m0,em⟩ := jet1 m hm
    rw [ej,ek,el,em]
    have he : (j3 (E a_j0) (E a_j1) (E a_j2))*(field)*(field)*(j1 (E a_m0)) = word 1 (E a_j0) (E a_j1) (E a_j2) (E a_m0) := by
      change (j3 (E a_j0) (E a_j1) (E a_j2))*(field)*(field)*(j1 (E a_m0)) = field^2*(j3 (E a_j0) (E a_j1) (E a_j2))*(j1 (E a_m0))
      ring
    rw [he]
    exact word_mem 1 a_j0 a_j1 a_j2 a_m0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,a_j2,ej⟩ := jet3 j hj
    have ek := jet0 k hk
    obtain ⟨a_l0,el⟩ := jet1 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j3 (E a_j0) (E a_j1) (E a_j2))*(field)*(j1 (E a_l0))*(field) = word 1 (E a_j0) (E a_j1) (E a_j2) (E a_l0) := by
      change (j3 (E a_j0) (E a_j1) (E a_j2))*(field)*(j1 (E a_l0))*(field) = field^2*(j3 (E a_j0) (E a_j1) (E a_j2))*(j1 (E a_l0))
      ring
    rw [he]
    exact word_mem 1 a_j0 a_j1 a_j2 a_l0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,a_j2,ej⟩ := jet3 j hj
    obtain ⟨a_k0,ek⟩ := jet1 k hk
    have el := jet0 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j3 (E a_j0) (E a_j1) (E a_j2))*(j1 (E a_k0))*(field)*(field) = word 1 (E a_j0) (E a_j1) (E a_j2) (E a_k0) := by
      change (j3 (E a_j0) (E a_j1) (E a_j2))*(j1 (E a_k0))*(field)*(field) = field^2*(j3 (E a_j0) (E a_j1) (E a_j2))*(j1 (E a_k0))
      ring
    rw [he]
    exact word_mem 1 a_j0 a_j1 a_j2 a_k0
  · obtain ⟨hj,hk,hl,hm⟩ := h
    obtain ⟨a_j0,a_j1,a_j2,a_j3,ej⟩ := jet4 j hj
    have ek := jet0 k hk
    have el := jet0 l hl
    have em := jet0 m hm
    rw [ej,ek,el,em]
    have he : (j4 (E a_j0) (E a_j1) (E a_j2) (E a_j3))*(field)*(field)*(field) = word 0 (E a_j0) (E a_j1) (E a_j2) (E a_j3) := by
      change (j4 (E a_j0) (E a_j1) (E a_j2) (E a_j3))*(field)*(field)*(field) = field^3*(j4 (E a_j0) (E a_j1) (E a_j2) (E a_j3))
      ring
    rw [he]
    exact word_mem 0 a_j0 a_j1 a_j2 a_j3

theorem grade_eq_span : V = wordSpan := by
  apply le_antisymm
  · intro p hp
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro a ha
    have hw := hp (MvPolynomial.mem_support_iff.mp ha)
    obtain ⟨j,k,l,m,he,hd⟩ := ScalarDegreeFour.monomial_four hw
    have hc : (monomial a (p.coeff a) : OffShell) = p.coeff a • monomial a 1 := by simp [smul_monomial]
    rw [hc,he]
    exact wordSpan.smul_mem _ (product_mem j k l m hd)
  · apply Submodule.span_le.mpr
    rintro p ⟨r,i,j,k,l,rfl⟩
    exact word_grade r (E i) (E j) (E k) (E l)

end
end Physics.ScalarQuarticFourSource
